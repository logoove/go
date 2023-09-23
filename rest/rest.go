/**
一个简单的go框架，复制的是github开源，并非自己写的
20230831
**/
package rest

import (
	"bytes"
	"encoding/json"
	"encoding/xml"
	"fmt"
	"io/ioutil"
	"log"
	"net"
	"net/http"
	"net/url"
	"os"
	"reflect"
	"strconv"
	"strings"
)

var (
	IndentJSON string
	Log = log.Println
	DontCheckRequestMethod bool
)
func HandleGET(path string, handler interface{}, object ...interface{}) {
	handlerFunc, in, out := getHandlerFunc(handler, object)
	httpHandler := &httpHandler{
		method:      "GET",
		handlerFunc: handlerFunc,
	}
	switch len(in) {
	case 0:
		httpHandler.getArgs = func(request *http.Request) []reflect.Value {
			return nil
		}
	case 1:
		if in[0] != reflect.TypeOf(url.Values(nil)) {
			panic(fmt.Errorf("HandleGET(): handler argument must be url.Values, got %s", in[0]))
		}
		httpHandler.getArgs = func(request *http.Request) []reflect.Value {
			return []reflect.Value{reflect.ValueOf(request.URL.Query())}
		}
	default:
		panic(fmt.Errorf("HandleGET(): handler accepts zero or one arguments, got %d", len(in)))
	}
	httpHandler.writeResult = writeResultFunc(out)
	http.Handle(path, httpHandler)
}
func HandlePOST(path string, handler interface{}, object ...interface{}) {
	handlerFunc, in, out := getHandlerFunc(handler, object)
	httpHandler := &httpHandler{
		method:      "POST",
		handlerFunc: handlerFunc,
	}
	switch len(in) {
	case 1:
		a := in[0]
		if a != urlValuesType && (a.Kind() != reflect.Ptr || a.Elem().Kind() != reflect.Struct) && a.Kind() != reflect.String {
			panic(fmt.Errorf("HandlePOST(): first handler argument must be a struct pointer, string, or url.Values. Got %s", a))
		}
		httpHandler.getArgs = func(request *http.Request) []reflect.Value {
			ct := request.Header.Get("Content-Type")
			switch ct {
			case "", "application/x-www-form-urlencoded":
				request.ParseForm()
				if a == urlValuesType {
					return []reflect.Value{reflect.ValueOf(request.Form)}
				}
				s := reflect.New(a.Elem())
				if len(request.Form) == 1 && request.Form.Get("JSON") != "" {
					err := json.Unmarshal([]byte(request.Form.Get("JSON")), s.Interface())
					if err != nil {
						panic(err)
					}
				} else {
					v := s.Elem()
					for key, value := range request.Form {
						if f := v.FieldByName(key); f.IsValid() && f.CanSet() {
							switch f.Kind() {
							case reflect.String:
								f.SetString(value[0])
							case reflect.Bool:
								if val, err := strconv.ParseBool(value[0]); err == nil {
									f.SetBool(val)
								}
							case reflect.Float32, reflect.Float64:
								if val, err := strconv.ParseFloat(value[0], 64); err == nil {
									f.SetFloat(val)
								}
							case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
								if val, err := strconv.ParseInt(value[0], 0, 64); err == nil {
									f.SetInt(val)
								}
							case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64:
								if val, err := strconv.ParseUint(value[0], 0, 64); err == nil {
									f.SetUint(val)
								}
							}
						}
					}
				}
				return []reflect.Value{s}

			case "text/plain":
				if a.Kind() != reflect.String {
					panic(fmt.Errorf("HandlePOST(): first handler argument must be a string when request Content-Type is text/plain, got %s", a))
				}
				defer request.Body.Close()
				body, err := ioutil.ReadAll(request.Body)
				if err != nil {
					panic(err)
				}
				return []reflect.Value{reflect.ValueOf(string(body))}

			case "application/xml":
				if a.Kind() != reflect.Ptr || a.Elem().Kind() != reflect.Struct {
					panic(fmt.Errorf("HandlePOST(): first handler argument must be a struct pointer when request Content-Type is application/xml, got %s", a))
				}
				s := reflect.New(a.Elem())
				defer request.Body.Close()
				body, err := ioutil.ReadAll(request.Body)
				if err != nil {
					panic(err)
				}
				err = xml.Unmarshal(body, s.Interface())
				if err != nil {
					panic(err)
				}
				return []reflect.Value{s}

			case "application/json":
				if a.Kind() != reflect.Ptr || a.Elem().Kind() != reflect.Struct {
					panic(fmt.Errorf("HandlePOST(): first handler argument must be a struct pointer when request Content-Type is application/json, got %s", a))
				}
				s := reflect.New(a.Elem())
				defer request.Body.Close()
				body, err := ioutil.ReadAll(request.Body)
				if err != nil {
					panic(err)
				}
				err = json.Unmarshal(body, s.Interface())
				if err != nil {
					panic(err)
				}
				return []reflect.Value{s}

			case "multipart/form-data":
				if a.Kind() != reflect.Ptr || a.Elem().Kind() != reflect.Struct {
					panic(fmt.Errorf("HandlePOST(): first handler argument must be a struct pointer when request Content-Type is multipart/form-data, got %s", a))
				}
				file, _, err := request.FormFile("JSON")
				if err != nil {
					panic(err)
				}
				s := reflect.New(a.Elem())
				defer file.Close()
				body, err := ioutil.ReadAll(request.Body)
				if err != nil {
					panic(err)
				}
				err = json.Unmarshal(body, s.Interface())
				if err != nil {
					panic(err)
				}
				return []reflect.Value{s}
			}
			panic("Unsupported POST Content-Type: " + ct)
		}
	default:
		panic(fmt.Errorf("HandlePOST(): handler accepts only one or thwo arguments, got %d", len(in)))
	}
	httpHandler.writeResult = writeResultFunc(out)
	http.Handle(path, httpHandler)
}
func RunServer(addr string, stop chan struct{}) {
	server := &http.Server{Addr: addr}
	listener, err := net.Listen("tcp", addr)
	if err != nil {
		panic(err)
	}
	if stop != nil {
		go func() {
			<-stop
			err := listener.Close()
			if err != nil {
				os.Stderr.WriteString(err.Error())
			}
			return
		}()
	}
	Log("Server listening at", addr)
	err = server.Serve(listener)
	if !strings.Contains(err.Error(), "use of closed network connection") {
		panic(err)
	}
	Log("Server stopped")
}
func getHandlerFunc(handler interface{}, object []interface{}) (f reflectionFunc, in, out []reflect.Type) {
	handlerValue := reflect.ValueOf(handler)
	if handlerValue.Kind() != reflect.Func {
		panic(fmt.Errorf("handler must be a function, got %T", handler))
	}
	handlerType := handlerValue.Type()
	out = make([]reflect.Type, handlerType.NumOut())
	for i := 0; i < handlerType.NumOut(); i++ {
		out[i] = handlerType.Out(i)
	}
	switch len(object) {
	case 0:
		f = func(args []reflect.Value) []reflect.Value {
			return handlerValue.Call(args)
		}
		in = make([]reflect.Type, handlerType.NumIn())
		for i := 0; i < handlerType.NumIn(); i++ {
			in[i] = handlerType.In(i)
		}
		return f, in, out
	case 1:
		objectValue := reflect.ValueOf(object[0])
		if objectValue.Kind() != reflect.Ptr {
			panic(fmt.Errorf("object must be a pointer, got %T", objectValue.Interface()))
		}
		f = func(args []reflect.Value) []reflect.Value {
			args = append([]reflect.Value{objectValue}, args...)
			return handlerValue.Call(args)
		}
		in = make([]reflect.Type, handlerType.NumIn()-1)
		for i := 1; i < handlerType.NumIn(); i++ {
			in[i] = handlerType.In(i)
		}
		return f, in, out
	}
	panic(fmt.Errorf("HandleGET(): only zero or one object allowed, got %d", len(object)))
}

var (
	urlValuesType = reflect.TypeOf((*url.Values)(nil)).Elem()
	errorType     = reflect.TypeOf((*error)(nil)).Elem()
)

type reflectionFunc func([]reflect.Value) []reflect.Value

type httpHandler struct {
	method      string
	getArgs     func(*http.Request) []reflect.Value
	handlerFunc reflectionFunc
	writeResult func([]reflect.Value, http.ResponseWriter)
}

func (handler *httpHandler) ServeHTTP(writer http.ResponseWriter, request *http.Request) {
	Log(request.Method, request.URL)
	if !DontCheckRequestMethod && request.Method != handler.method {
		http.Error(writer, "405: Method Not Allowed", http.StatusMethodNotAllowed)
		return
	}
	result := handler.handlerFunc(handler.getArgs(request))
	handler.writeResult(result, writer)
}

func writeError(writer http.ResponseWriter, err error) {
	Log("ERROR:", err)
	http.Error(writer, err.Error(), http.StatusInternalServerError)
}

func writeResultFunc(out []reflect.Type) func([]reflect.Value, http.ResponseWriter) {
	var returnError func(result []reflect.Value, writer http.ResponseWriter) bool
	switch len(out) {
	case 2:
		if out[1] == errorType {
			returnError = func(result []reflect.Value, writer http.ResponseWriter) (isError bool) {
				if isError = !result[1].IsNil(); isError {
					writeError(writer, result[1].Interface().(error))
				}
				return isError
			}
		} else {
			panic(fmt.Errorf("HandleGET(): second result value of handle must be of type error, got %s", out[1]))
		}
		fallthrough
	case 1:
		r := out[0]
		if r.Kind() == reflect.Struct || (r.Kind() == reflect.Ptr && r.Elem().Kind() == reflect.Struct) {
			return func(result []reflect.Value, writer http.ResponseWriter) {
				if returnError != nil && returnError(result, writer) {
					return
				}
				j, err := json.Marshal(result[0].Interface())
				if err != nil {
					writeError(writer, err)
					return
				}
				if IndentJSON != "" {
					var buf bytes.Buffer
					err = json.Indent(&buf, j, "", IndentJSON)
					if err != nil {
						writeError(writer, err)
						return
					}
					j = buf.Bytes()
				}
				writer.Header().Set("Content-Type", "application/json")
				writer.Write(j)
			}
		} else if r.Kind() == reflect.String {
			return func(result []reflect.Value, writer http.ResponseWriter) {
				if returnError != nil && returnError(result, writer) {
					return
				}
				bytes := []byte(result[0].String())
				ct := http.DetectContentType(bytes)
				writer.Header().Set("Content-Type", ct)
				writer.Write(bytes)
			}
		} else {
			panic(fmt.Errorf("first result value of handler must be of type string or struct(pointer), got %s", r))
		}
	case 0:
		return func(result []reflect.Value, writer http.ResponseWriter) {
		}
	}
	panic(fmt.Errorf("zero to two return values allowed, got %d", len(out)))
}
func GetJSON(addr string, out interface{}) error {
	response, err := http.Get(addr)
	if err != nil {
		return err
	}
	defer response.Body.Close()
	body, err := ioutil.ReadAll(response.Body)
	if err != nil {
		return err
	}
	return json.Unmarshal(body, out)
}
func GetJSONStrict(addr string, out interface{}) error {
	response, err := http.Get(addr)
	if err != nil {
		return err
	}
	if ct := response.Header.Get("Content-Type"); ct != "application/json" {
		return fmt.Errorf("GetJSONStrict expected Content-Type 'application/json', but got '%s'", ct)
	}
	defer response.Body.Close()
	body, err := ioutil.ReadAll(response.Body)
	if err != nil {
		return err
	}
	return json.Unmarshal(body, out)
}
