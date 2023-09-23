package yo

import (
	"archive/zip"
	"bufio"
	"bytes"
	"crypto/aes"
	"crypto/cipher"
	"crypto/md5"
	crand "crypto/rand"
	"crypto/sha1"
	"crypto/sha256"
	"encoding/base64"
	"encoding/binary"
	"encoding/csv"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"html"
	"io"
	"math"
	"math/rand"
	"net"
	"net/http"
	"net/smtp"
	"net/url"
	"os"
	"os/exec"
	"path"
	"path/filepath"
	"reflect"
	"regexp"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"time"
	"unicode"
	"unicode/utf8"
)

type Signed interface {
	~int | ~int8 | ~int16 | ~int32 | ~int64
}
type Unsigned interface {
	~uint | ~uint8 | ~uint16 | ~uint32 | ~uint64 | ~uintptr
}
type Integer interface {
	Signed | Unsigned
}
type Float interface {
	~float32 | ~float64
}
type Complex interface {
	~complex64 | ~complex128
}
type Ordered interface {
	Integer | Float | ~string
}

// Uniq[T comparable]
// Uniq([]string{"Samuel", "John", "Samuel"})
//
//	@Description: 去除scile中重复元素
//	@param collection
//	@return []T
func Uniq[T comparable](collection []T) []T {
	result := make([]T, 0, len(collection))
	seen := make(map[T]struct{}, len(collection))

	for _, item := range collection {
		if _, ok := seen[item]; ok {
			continue
		}

		seen[item] = struct{}{}
		result = append(result, item)
	}

	return result
}

// Merge[T any]
//
//	@Description: 合并多个切片,同元素存在
//	@param slices
//	@return []T
func Merge[T any](slices ...[]T) []T {
	result := make([]T, 0)

	for _, v := range slices {
		result = append(result, v...)
	}

	return result
}

// Union[T comparable]
//
//	@Description: 合并多个切片,相同元素也会合并
//	@param slices
//	@return []T
func Union[T comparable](slices ...[]T) []T {
	result := []T{}
	contain := map[T]struct{}{}

	for _, slice := range slices {
		for _, item := range slice {
			if _, ok := contain[item]; !ok {
				contain[item] = struct{}{}
				result = append(result, item)
			}
		}
	}

	return result
}

// 是否升序
func IsAsc[T Ordered](slice []T) bool {
	for i := 1; i < len(slice); i++ {
		if slice[i-1] > slice[i] {
			return false
		}
	}

	return true
}

// 是否降序
func IsDesc[T Ordered](slice []T) bool {
	for i := 1; i < len(slice); i++ {
		if slice[i-1] < slice[i] {
			return false
		}
	}

	return true
}

// 检查切片元素是否是有序的（升序或降序）
func IsSorted[T Ordered](slice []T) bool {
	return IsAsc(slice) || IsDesc(slice)
}

// Sort[T Ordered]
//
//	@Description: 对任何有序类型（数字或字符串）的切片进行排序，使用快速排序算法
//	@param slice
//	@param sortOrder
func Sort[T Ordered](slice []T, sortOrder ...string) {
	if len(sortOrder) > 0 && sortOrder[0] == "desc" {
		quickSort(slice, 0, len(slice)-1, "desc")
	} else {
		quickSort(slice, 0, len(slice)-1, "asc")
	}
}
func quickSort[T Ordered](slice []T, lowIndex, highIndex int, order string) {
	if lowIndex < highIndex {
		p := partitionOrderedSlice(slice, lowIndex, highIndex, order)
		quickSort(slice, lowIndex, p-1, order)
		quickSort(slice, p+1, highIndex, order)
	}
}
func partitionOrderedSlice[T Ordered](slice []T, lowIndex, highIndex int, order string) int {
	p := slice[highIndex]
	i := lowIndex

	for j := lowIndex; j < highIndex; j++ {
		if order == "desc" {
			if slice[j] > p {
				swap(slice, i, j)
				i++
			}
		} else {
			if slice[j] < p {
				swap(slice, i, j)
				i++
			}
		}
	}

	swap(slice, i, highIndex)

	return i
}
func swap[T any](slice []T, i, j int) {
	slice[i], slice[j] = slice[j], slice[i]
}

// Filter[V any]
// Filter([]int64{1, 2, 3, 4},func(a int64,i int)bool{ 返回被2整除
// return a%2 ==0
// })
//
//	@Description:刷选集合中元素
//	@param collection
//	@param predicate
//	@return []V
func Filter[V any](collection []V, predicate func(item V, index int) bool) []V {
	result := make([]V, 0, len(collection))

	for i, item := range collection {
		if predicate(item, i) {
			result = append(result, item)
		}
	}

	return result
}

// ForEach[T any]
//
//	@Description: scile循环处理
//	@param collection item值 index是key
//	@param iteratee
func ForEach[T any](collection []T, iteratee func(item T, index int)) {
	for i, item := range collection {
		iteratee(item, i)
	}
}

// Map[T any, U any]
//
//	@Description:对 slice 中的每个元素执行 map 函数以创建一个新切片
//	@param slice Map(nums,func(_ int, v int) int {
//		return v + 1
//	})
//	@param iteratee
//	@return []U
func Map[T any, U any](slice []T, iteratee func(index int, item T) U) []U {
	result := make([]U, len(slice), cap(slice))

	for i := 0; i < len(slice); i++ {
		result[i] = iteratee(i, slice[i])
	}

	return result
}

// Join[T any]
//
//	@Description:用指定的分隔符链接切片元素
//	@param slice 切片转换字符串
//	@param separator Join(nums, ",")
//	@return string
func Join[T any](slice []T, separator string) string {
	str := Map(slice, func(_ int, item T) string {
		return fmt.Sprint(item)
	})

	return strings.Join(str, separator)
}

// InsertAt[T any]
//
//	@Description: 在scile索引位置插入值
//	@param slice
//	@param index
//	@param value
//	@return []T
func InsertAt[T any](slice []T, index int, value any) []T {
	size := len(slice)

	if index < 0 || index > size {
		return slice
	}

	if v, ok := value.(T); ok {
		slice = append(slice[:index], append([]T{v}, slice[index:]...)...)
		return slice
	}

	if v, ok := value.([]T); ok {
		slice = append(slice[:index], append(v, slice[index:]...)...)
		return slice
	}

	return slice
}

// Associate[T any, K comparable, V any]
//
//	@Description: scile处理成map
//
//	Associate([]string("a","bb","cc"), func(str string) (string, int) {
//		return str, len(str)
//	})
//
//	@param collection
//	@param transform
//	@return map[K]V
func Associate[T any, K comparable, V any](collection []T, transform func(item T) (K, V)) map[K]V {
	result := make(map[K]V, len(collection))

	for _, t := range collection {
		k, v := transform(t)
		result[k] = v
	}

	return result
}

// SliceToMap[T any, K comparable, V any]
//
//	@Description:切片转换字典
//	@param collection
//	@param transform
//	@return map[K]V
func SliceToMap[T any, K comparable, V any](collection []T, transform func(item T) (K, V)) map[K]V {
	return Associate(collection, transform)
}

// IsEmpty[T comparable]
//
//	@Description: 是否为空 0 "" 是空
//	@param v
//	@return bool
func IsEmpty[T comparable](v T) bool {
	var zero T
	return zero == v
}

// ------------------字典开始-----------------------
// Keys[K comparable, V any]
//
//	@Description: 返回字典key
//	@param in
//	@return []K
func Keys[K comparable, V any](in map[K]V) []K {
	result := make([]K, 0, len(in))

	for k := range in {
		result = append(result, k)
	}

	return result
}

// Values[K comparable, V any]
//
//	@Description: 返回字典值
//	@param in
//	@return []V
func Values[K comparable, V any](in map[K]V) []V {
	result := make([]V, 0, len(in))

	for _, v := range in {
		result = append(result, v)
	}

	return result
}

// 合并多个map
func MergeMap[K comparable, V any](maps ...map[K]V) map[K]V {
	result := make(map[K]V, 0)

	for _, m := range maps {
		for k, v := range m {
			result[k] = v
		}
	}

	return result
}

// HasKey[K comparable, V any]
//
//	@Description:检查 map 是否包含某个 key
//	@param m mp := map[string]string{"a": "中国", "b": "日本"}
//	fmt.Println(yo.HasKey(mp, "a"))
//	@param key
//	@return bool
func HasKey[K comparable, V any](m map[K]V, key K) bool {
	_, haskey := m[key]
	return haskey
}

// Invert[K comparable, V comparable]
// kv := map[string]int{"foo": 1, "bar": 2, "baz": 3, "new": 3}
//
//	@Description: 键值交换
//	@param in
//	@return map[V]K
func Invert[K comparable, V comparable](in map[K]V) map[V]K {
	out := make(map[V]K, len(in))

	for k, v := range in {
		out[v] = k
	}

	return out
}
func FilterMap[K comparable, V any](m map[K]V, predicate func(key K, value V) bool) map[K]V {
	result := make(map[K]V)

	for k, v := range m {
		if predicate(k, v) {
			result[k] = v
		}
	}
	return result
}

// 处理map
func ForEachMap[K comparable, V any](m map[K]V, iteratee func(key K, value V)) {
	for k, v := range m {
		iteratee(k, v)
	}
}

// MapToSlice[K comparable, V any, R any]
//
//	@Description: map转换scile,可以自己处理逻辑
//	@param in
//	@param iteratee
//	@return []R
func MapToSlice[K comparable, V any, R any](in map[K]V, iteratee func(key K, value V) R) []R {
	result := make([]R, 0, len(in))

	for k, v := range in {
		result = append(result, iteratee(k, v))
	}

	return result
}

// RandomString
//
//	@Description: 随机字符串
//	@param size 长度
//	@param charset
//	@return string
func RandomString(size int, charset []rune) string {
	if size <= 0 {
		panic("RandomString: Size parameter must be greater than 0")
	}
	if len(charset) <= 0 {
		charset = []rune("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789")
	}

	b := make([]rune, size)
	possibleCharactersCount := len(charset)
	for i := range b {
		b[i] = charset[rand.Intn(possibleCharactersCount)]
	}
	return string(b)
}

// RuneLength
//
//	@Description: 计算中文字符长度,len中文算3个,这个算1个
//	@param str
//	@return int
func RuneLength(str string) int {
	return utf8.RuneCountInString(str)
}

// Reverse[T any]
//
//	@Description: sclie反序
//	@param collection
//	@return []T
func Reverse[T any](collection []T) []T {
	length := len(collection)
	half := length / 2

	for i := 0; i < half; i = i + 1 {
		j := length - 1 - i
		collection[i], collection[j] = collection[j], collection[i]
	}

	return collection
}

// Chunk[T any]
// Chunk([]int(1,2,3,4), 2) [1,2] [3,4]
//
//	@Description: 分割数组,切片，按照个数组成新的切片
//	@param collection
//	@param size
//	@return [][]T
func Chunk[T any](collection []T, size int) [][]T {
	if size <= 0 {
		panic("Second parameter must be greater than 0")
	}

	chunksNum := len(collection) / size
	if len(collection)%size != 0 {
		chunksNum += 1
	}

	result := make([][]T, 0, chunksNum)

	for i := 0; i < chunksNum; i++ {
		last := (i + 1) * size
		if last > len(collection) {
			last = len(collection)
		}
		result = append(result, collection[i*size:last])
	}

	return result
}

// ChunkString[T ~string]
// ChunkString("123456", 2) [1,2][3,4][5,6]
//
//	@Description: 分割字符串
//	@param str
//	@param size
//	@return []T
func ChunkString[T ~string](str T, size int) []T {
	if size <= 0 {
		panic("ChunkString: Size parameter must be greater than 0")
	}

	if len(str) == 0 {
		return []T{""}
	}

	if size >= len(str) {
		return []T{str}
	}

	var chunks []T = make([]T, 0, ((len(str)-1)/size)+1)
	currentLen := 0
	currentStart := 0
	for i := range str {
		if currentLen == size {
			chunks = append(chunks, str[currentStart:i])
			currentLen = 0
			currentStart = i
		}
		currentLen++
	}
	chunks = append(chunks, str[currentStart:])
	return chunks
}

// Compact[T comparable]
// []string{"", "foo", "", "bar", ""} 返回["foo","bar"]
//
//	@Description: 返回非空切片的新切片
//	@param collection
//	@return []T
func Compact[T comparable](collection []T) []T {
	var zero T

	result := make([]T, 0, len(collection))

	for _, item := range collection {
		if item != zero {
			result = append(result, item)
		}
	}

	return result
}

// Contains[T comparable]
//
//	@Description: 判断sclie是否包含元素
//	@param collection
//	@param element
//	@return bool
func Contain[T comparable](slice []T, target T) bool {
	for _, item := range slice {
		if item == target {
			return true
		}
	}

	return false
}

// 是否包含子切片
func ContainSubSlice[T comparable](slice, subSlice []T) bool {
	for _, v := range subSlice {
		if !Contain(slice, v) {
			return false
		}
	}

	return true
}

// Drop[T any]
//
//	@Description: 删除scile元素,左边开始,返回新的
//	@param collection
//	@param n
//	@return []T
func Drop[T any](collection []T, n int) []T {
	if len(collection) <= n {
		return make([]T, 0)
	}

	result := make([]T, 0, len(collection)-n)

	return append(result, collection[n:]...)
}

// 从右边删除,返回删除后的新切片
func DropRight[T any](collection []T, n int) []T {
	if len(collection) <= n {
		return []T{}
	}

	result := make([]T, 0, len(collection)-n)
	return append(result, collection[:len(collection)-n]...)
}

// DropWhile[T any]
//
//	@Description: 左边开始条件删除
//	@param collection
//	DropWhile(list, func(val int) bool {
//		return val > 2
//	})
//	@return []T
func DropWhile[T any](collection []T, predicate func(item T) bool) []T {
	i := 0
	for ; i < len(collection); i++ {
		if !predicate(collection[i]) {
			break
		}
	}

	result := make([]T, 0, len(collection)-i)
	return append(result, collection[i:]...)
}

// 右边条件删除
func DropRightWhile[T any](collection []T, predicate func(item T) bool) []T {
	i := len(collection) - 1
	for ; i >= 0; i-- {
		if !predicate(collection[i]) {
			break
		}
	}

	result := make([]T, 0, i+1)
	return append(result, collection[:i+1]...)
}

// Flatten[T any]
// [][]int{{0, 1, 2}, {3, 4, 5}}=> [0,1,2,3,4,5]
//
//	@Description: 转换数组维度
//	@param collection
//	@return []T
func Flatten[T any](collection [][]T) []T {
	totalLen := 0
	for i := range collection {
		totalLen += len(collection[i])
	}

	result := make([]T, 0, totalLen)
	for i := range collection {
		result = append(result, collection[i]...)
	}

	return result
}

// Intersect[T comparable]
// list1 := []int{0, 1, 2, 3, 4, 3}
//
//	list2 := []int{3, 4, 3}
//	@Description: 两个切片 交集
//	@param list1
//	@param list2
//	@return []T
func Intersect[T comparable](list1 []T, list2 []T) []T {
	result := []T{}
	seen := map[T]struct{}{}

	for _, elem := range list1 {
		seen[elem] = struct{}{}
	}

	for _, elem := range list2 {
		if _, ok := seen[elem]; ok {
			result = append(result, elem)
		}
	}

	return result
}

// Last[T any]
//
//	@Description: 返回最后一个值
//	@param collection
//	@return T
//	@return error
func Last[T any](collection []T) (T, error) {
	length := len(collection)

	if length == 0 {
		var t T
		return t, fmt.Errorf("last: cannot extract the last element of an empty slice")
	}

	return collection[length-1], nil
}
func Empty[T any]() T {
	var zero T
	return zero
}

// Sample[T any]
//
//	@Description: 随机返回一个值
//
// []int64{1,2,3}
//
//	@param collection
//	@return T
func Sample[T any](collection []T) T {
	size := len(collection)
	if size == 0 {
		return Empty[T]()
	}

	return collection[rand.Intn(size)]
}

// Samples[T any]
//
//	@Description: 随即返回指定个数scile
//	@param collection
//	@param count
//	@return []T
func Samples[T any](collection []T, count int) []T {
	size := len(collection)

	var copy1 = append([]T{}, collection...)
	results := []T{}

	for i := 0; i < size && i < count; i++ {
		copyLength := size - i

		index := rand.Intn(size - i)
		results = append(results, copy1[index])
		copy1[index] = copy1[copyLength-1]
		copy1 = copy1[:copyLength-1]
	}

	return results
}

// Shuffle[T any]
// Shuffle([]string{"a", "bb", "c", "ee"})
//
//	@Description: 打乱数组
//	@param collection
//	@return []T
func Shuffle[T any](collection []T) []T {
	rand.Shuffle(len(collection), func(i, j int) {
		collection[i], collection[j] = collection[j], collection[i]
	})

	return collection
}

// Ternary[T any]
//
//	@Description: 三元运算符 字符串
//	@param condition
//	@param ifOutput
//	@param elseOutput
//	@return T
func Ternary[T any](condition bool, ifOutput T, elseOutput T) T {
	if condition {
		return ifOutput
	}

	return elseOutput
}

// TernaryF[T any]
//
//	@Description: 三元运算符函数
//	@param condition
//	@param ifFunc
//	@param elseFunc
//	@return T
func TernaryF[T any](condition bool, ifFunc func() T, elseFunc func() T) T {
	if condition {
		return ifFunc()
	}

	return elseFunc()
}

/**
 * @Description: 将utf-8编码的字符串转换为GBK编码
 * @param str 要转换字符串
 * @return string
 */
func Utf2Gbk(str string) string {
	ret, _ := GBK.NewEncoder().String(str)
	return ret
	b, _ := GBK.NewEncoder().Bytes([]byte(str))
	return string(b)
}

/**
 * @Description: 将GBK编码的字符串转换为utf-8编码
 * @param gbkStr
 * @return string
 */
func Gbk2Utf8(gbkStr string) string {
	ret, _ := GBK.NewDecoder().String(gbkStr)
	return ret
	b, _ := GBK.NewDecoder().Bytes([]byte(gbkStr))
	return string(b)
}

// 转换成布尔
func ToBool(s string) (bool, error) {
	return strconv.ParseBool(s)
}

// 转换字节 ToChar("abc") [a,b,c]
func ToChar(s string) []string {
	c := make([]string, 0)
	if len(s) == 0 {
		c = append(c, "")
	}
	for _, v := range s {
		c = append(c, string(v))
	}
	return c
}

// ToFloat
//
//	@Description: 转换成浮点数 float64
//	@param value
//	@return float64
//	@return error
func ToFloat(value any) (float64, error) {
	v := reflect.ValueOf(value)

	result := 0.0
	err := fmt.Errorf("ToInt: unvalid interface type %T", value)
	switch value.(type) {
	case int, int8, int16, int32, int64:
		result = float64(v.Int())
		return result, nil
	case uint, uint8, uint16, uint32, uint64:
		result = float64(v.Uint())
		return result, nil
	case float32, float64:
		result = v.Float()
		return result, nil
	case string:
		result, err = strconv.ParseFloat(v.String(), 64)
		if err != nil {
			result = 0.0
		}
		return result, err
	default:
		return result, err
	}
}

// ToInt
//
//	@Description: 转换成int64
//	@param value
//	@return int64
//	@return error
func ToInt(value any) (int64, error) {
	v := reflect.ValueOf(value)

	var result int64
	err := fmt.Errorf("ToInt: invalid value type %T", value)
	switch value.(type) {
	case int, int8, int16, int32, int64:
		result = v.Int()
		return result, nil
	case uint, uint8, uint16, uint32, uint64:
		result = int64(v.Uint())
		return result, nil
	case float32, float64:
		result = int64(v.Float())
		return result, nil
	case string:
		result, err = strconv.ParseInt(v.String(), 0, 64)
		if err != nil {
			result = 0
		}
		return result, err
	default:
		return result, err
	}
}

// ToString
//
//	@Description: 将值转换为字符串，对于数字、字符串、[]byte，将转换为字符串。 对于其他类型（切片、映射、数组、结构）将调用 json.Marshal
//	@param value
//	@return string
func ToString(value any) string {
	if value == nil {
		return ""
	}

	switch val := value.(type) {
	case float32:
		return strconv.FormatFloat(float64(val), 'f', -1, 32)
	case float64:
		return strconv.FormatFloat(val, 'f', -1, 64)
	case int:
		return strconv.FormatInt(int64(val), 10)
	case int8:
		return strconv.FormatInt(int64(val), 10)
	case int16:
		return strconv.FormatInt(int64(val), 10)
	case int32:
		return strconv.FormatInt(int64(val), 10)
	case int64:
		return strconv.FormatInt(val, 10)
	case uint:
		return strconv.FormatUint(uint64(val), 10)
	case uint8:
		return strconv.FormatUint(uint64(val), 10)
	case uint16:
		return strconv.FormatUint(uint64(val), 10)
	case uint32:
		return strconv.FormatUint(uint64(val), 10)
	case uint64:
		return strconv.FormatUint(val, 10)
	case string:
		return val
	case []byte:
		return string(val)
	default:
		b, err := json.Marshal(val)
		if err != nil {
			return ""
		}
		return string(b)

		// todo: maybe we should't supprt other type conversion
		// v := reflect.ValueOf(value)
		// log.Panicf("Unsupported data type: %s ", v.String())
		// return ""
	}
}

// ToBytes
//
//	@Description: interface 转字节切片
//	@param value
//	@return []byte
//	@return error
func ToBytes(value any) ([]byte, error) {
	v := reflect.ValueOf(value)

	switch value.(type) {
	case int, int8, int16, int32, int64:
		number := v.Int()
		buf := bytes.NewBuffer([]byte{})
		buf.Reset()
		err := binary.Write(buf, binary.BigEndian, number)
		return buf.Bytes(), err
	case uint, uint8, uint16, uint32, uint64:
		number := v.Uint()
		buf := bytes.NewBuffer([]byte{})
		buf.Reset()
		err := binary.Write(buf, binary.BigEndian, number)
		return buf.Bytes(), err
	case float32:
		number := float32(v.Float())
		bits := math.Float32bits(number)
		bytes := make([]byte, 4)
		binary.BigEndian.PutUint32(bytes, bits)
		return bytes, nil
	case float64:
		number := v.Float()
		bits := math.Float64bits(number)
		bytes := make([]byte, 8)
		binary.BigEndian.PutUint64(bytes, bits)
		return bytes, nil
	case bool:
		return strconv.AppendBool([]byte{}, v.Bool()), nil
	case string:
		return []byte(v.String()), nil
	case []byte:
		return v.Bytes(), nil
	default:
		newValue, err := json.Marshal(value)
		return newValue, err
	}
}
func ToJson(value any) (string, error) {
	result, err := json.Marshal(value)
	if err != nil {
		return "", err
	}

	return string(result), nil
}

// ToMap[T any, K comparable, V any]
//
//	@Description:将切片转为 map
//	@param array
//	@param iteratee
//	@return map[K]V
func ToMap[T any, K comparable, V any](array []T, iteratee func(T) (K, V)) map[K]V {
	result := make(map[K]V, len(array))
	for _, item := range array {
		k, v := iteratee(item)
		result[k] = v
	}

	return result
}
func StructToMap(value any) map[string]any {
	t := reflect.TypeOf(value)
	v := reflect.ValueOf(value)

	var data = make(map[string]any)
	for i := 0; i < t.NumField(); i++ {
		data[t.Field(i).Name] = v.Field(i).Interface()
	}
	return data
}

// 颜色值十六进制转 rgb
func ColorHexToRGB(colorHex string) (red, green, blue int) {
	colorHex = strings.TrimPrefix(colorHex, "#")
	color64, err := strconv.ParseInt(colorHex, 16, 32)
	if err != nil {
		return
	}
	color := int(color64)
	return color >> 16, (color & 0x00FF00) >> 8, color & 0x0000FF
}

// 颜色值 rgb 转十六进制
func ColorRGBToHex(red, green, blue int) string {
	r := strconv.FormatInt(int64(red), 16)
	g := strconv.FormatInt(int64(green), 16)
	b := strconv.FormatInt(int64(blue), 16)

	if len(r) == 1 {
		r = "0" + r
	}
	if len(g) == 1 {
		g = "0" + g
	}
	if len(b) == 1 {
		b = "0" + b
	}

	return "#" + r + g + b
}

// ToInterface
// 将反射值转换成对应的 interface 类型
//
//	@Description:
//	@param v
//	@return value
//	@return ok
func ToInterface(v reflect.Value) (value interface{}, ok bool) {
	if v.IsValid() && v.CanInterface() {
		return v.Interface(), true
	}
	switch v.Kind() {
	case reflect.Bool:
		return v.Bool(), true
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		return v.Int(), true
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr:
		return v.Uint(), true
	case reflect.Float32, reflect.Float64:
		return v.Float(), true
	case reflect.Complex64, reflect.Complex128:
		return v.Complex(), true
	case reflect.String:
		return v.String(), true
	case reflect.Ptr:
		return ToInterface(v.Elem())
	case reflect.Interface:
		return ToInterface(v.Elem())
	default:
		return nil, false
	}
}
func Md5(s string) string {
	h := md5.New()
	h.Write([]byte(s))
	return hex.EncodeToString(h.Sum(nil))
}
func Sha1(str string) string {
	sha1 := sha1.New()
	sha1.Write([]byte(str))
	return hex.EncodeToString(sha1.Sum([]byte("")))
}
func Sha256(str string) string {
	sha256 := sha256.New()
	sha256.Write([]byte(str))
	return hex.EncodeToString(sha256.Sum([]byte("")))
}
func Base64Encode(s string, isurl bool) (s1 string) {
	if isurl == true {
		s1 = base64.URLEncoding.EncodeToString([]byte(s))
	} else {
		s1 = base64.StdEncoding.EncodeToString([]byte(s))
	}
	return s1
}

/**
 * @Description: 解码base64 str=php.Base64Decode(str,false)
 * @param s 要解码字符串
 * @param isurl 是否url
 * @return string
 */
func Base64Decode(s string, isurl bool) string {
	var s1 []byte
	x := len(s) * 3 % 4
	switch {
	case x == 2:
		s += "=="
	case x == 1:
		s += "="
	}
	if isurl == true {
		s1, _ = base64.URLEncoding.DecodeString(s)
	} else {
		s1, _ = base64.StdEncoding.DecodeString(s)
	}
	return string(s1)
}

// 判断文件或目录是否存在
func IsExist(path string) bool {
	_, err := os.Stat(path)
	if err == nil {
		return true
	}
	if errors.Is(err, os.ErrNotExist) {
		return false
	}
	return false
}

// 创建文件，创建成功返回 true, 否则返回 false
func CreateFile(path string) bool {
	file, err := os.Create(path)
	if err != nil {
		return false
	}

	defer file.Close()
	return true
}

// 创建嵌套目录，例如/a/, /a/b/
func CreateDir(absPath string) error {
	// return os.MkdirAll(path.Dir(absPath), os.ModePerm)
	return os.MkdirAll(absPath, os.ModePerm)
}

// 判断参数是否是目录
func IsDir(path string) bool {
	file, err := os.Stat(path)
	if err != nil {
		return false
	}
	return file.IsDir()
}

// 删除文件
func RemoveFile(path string) error {
	return os.Remove(path)
}

// 拷贝文件，会覆盖原有的文件
func CopyFile(srcPath string, dstPath string) error {
	srcFile, err := os.Open(srcPath)
	if err != nil {
		return err
	}
	defer srcFile.Close()

	distFile, err := os.Create(dstPath)
	if err != nil {
		return err
	}
	defer distFile.Close()

	var tmp = make([]byte, 1024*4)
	for {
		n, err := srcFile.Read(tmp)
		if err != nil {
			if err == io.EOF {
				return nil
			}
			return err
		}
		_, err = distFile.Write(tmp[:n])
		if err != nil {
			return err
		}
	}
}

// 读文件
func ReadFile(path string) (string, error) {
	bytes, err := os.ReadFile(path)
	if err != nil {
		return "", err
	}
	return string(bytes), nil
}

// 按行读取文件内容，返回字符串切片包含每一行
func ReadFileByLine(path string) ([]string, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()

	result := make([]string, 0)
	buf := bufio.NewReader(f)

	for {
		line, _, err := buf.ReadLine()
		l := string(line)
		if err == io.EOF {
			break
		}
		if err != nil {
			continue
		}
		result = append(result, l)
	}

	return result, nil
}

// 目录下所有文件名称
func ListFile(path string) ([]string, error) {
	if !IsExist(path) {
		return []string{}, nil
	}

	fs, err := os.ReadDir(path)
	if err != nil {
		return []string{}, err
	}

	sz := len(fs)
	if sz == 0 {
		return []string{}, nil
	}

	result := []string{}
	for i := 0; i < sz; i++ {
		if !fs[i].IsDir() {
			result = append(result, fs[i].Name())
		}
	}

	return result, nil
}

// 判断是否zip
func IsZipFile(filepath string) bool {
	f, err := os.Open(filepath)
	if err != nil {
		return false
	}
	defer f.Close()

	buf := make([]byte, 4)
	if n, err := f.Read(buf); err != nil || n < 4 {
		return false
	}

	return bytes.Equal(buf, []byte("PK\x03\x04"))
}

// 压缩文件 可以是文件或目录
func Zip(path string, destPath string) error {
	if IsDir(path) {
		return zipFolder(path, destPath)
	}

	return zipFile(path, destPath)
}

func zipFile(filePath string, destPath string) error {
	zipFile, err := os.Create(destPath)
	if err != nil {
		return err
	}
	defer zipFile.Close()

	archive := zip.NewWriter(zipFile)
	defer archive.Close()

	return addFileToArchive1(filePath, archive)
}

func zipFolder(folderPath string, destPath string) error {
	outFile, err := os.Create(destPath)
	if err != nil {
		return err
	}
	defer outFile.Close()

	w := zip.NewWriter(outFile)

	err = addFileToArchive2(w, folderPath, "")
	if err != nil {
		return err
	}

	err = w.Close()
	if err != nil {
		return err
	}

	return nil
}

func addFileToArchive1(fpath string, archive *zip.Writer) error {
	err := filepath.Walk(fpath, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}

		header, err := zip.FileInfoHeader(info)
		if err != nil {
			return err
		}

		header.Name = strings.TrimPrefix(path, filepath.Dir(fpath)+"/")

		if info.IsDir() {
			header.Name += "/"
		} else {
			header.Method = zip.Deflate
			writer, err := archive.CreateHeader(header)
			if err != nil {
				return err
			}
			file, err := os.Open(path)
			if err != nil {
				return err
			}
			defer file.Close()
			if _, err := io.Copy(writer, file); err != nil {
				return err
			}
		}
		return nil
	})
	return err
}

func addFileToArchive2(w *zip.Writer, basePath, baseInZip string) error {
	files, err := os.ReadDir(basePath)
	if err != nil {
		return err
	}
	if !strings.HasSuffix(basePath, "/") {
		basePath = basePath + "/"
	}

	for _, file := range files {
		if !file.IsDir() {
			dat, err := os.ReadFile(basePath + file.Name())
			if err != nil {
				return err
			}

			f, err := w.Create(baseInZip + file.Name())
			if err != nil {
				return err
			}
			_, err = f.Write(dat)
			if err != nil {
				return err
			}
		} else if file.IsDir() {
			newBase := basePath + file.Name() + "/"
			addFileToArchive2(w, newBase, baseInZip+file.Name()+"/")
		}
	}

	return nil
}

// 解压zip
func UnZip(zipFile string, destPath string) error {
	zipReader, err := zip.OpenReader(zipFile)
	if err != nil {
		return err
	}
	defer zipReader.Close()

	for _, f := range zipReader.File {
		//issue#62: fix ZipSlip bug
		path, err := safeFilepathJoin(destPath, f.Name)
		if err != nil {
			return err
		}

		if f.FileInfo().IsDir() {
			err = os.MkdirAll(path, os.ModePerm)
			if err != nil {
				return err
			}
		} else {
			err = os.MkdirAll(filepath.Dir(path), os.ModePerm)
			if err != nil {
				return err
			}

			inFile, err := f.Open()
			if err != nil {
				return err
			}
			defer inFile.Close()

			outFile, err := os.OpenFile(path, os.O_WRONLY|os.O_CREATE|os.O_TRUNC, f.Mode())
			if err != nil {
				return err
			}
			defer outFile.Close()

			_, err = io.Copy(outFile, inFile)
			if err != nil {
				return err
			}
		}
	}

	return nil
}

// 单个文件或目录添加到zip
func ZipAppendEntry(fpath string, destPath string) error {
	tempFile, err := os.CreateTemp("", "temp.zip")
	if err != nil {
		return err
	}
	defer os.Remove(tempFile.Name())

	zipReader, err := zip.OpenReader(destPath)
	if err != nil {
		return err
	}

	archive := zip.NewWriter(tempFile)

	for _, zipItem := range zipReader.File {
		zipItemReader, err := zipItem.Open()
		if err != nil {
			return err
		}
		header, err := zip.FileInfoHeader(zipItem.FileInfo())
		if err != nil {
			return err
		}
		header.Name = zipItem.Name
		targetItem, err := archive.CreateHeader(header)
		if err != nil {
			return err
		}
		_, err = io.Copy(targetItem, zipItemReader)
		if err != nil {
			return err
		}
	}

	err = addFileToArchive1(fpath, archive)

	if err != nil {
		return err
	}

	err = zipReader.Close()
	if err != nil {
		return err
	}
	err = archive.Close()
	if err != nil {
		return err
	}
	err = tempFile.Close()
	if err != nil {
		return err
	}

	return CopyFile(tempFile.Name(), destPath)
}
func safeFilepathJoin(path1, path2 string) (string, error) {
	relPath, err := filepath.Rel(".", path2)
	if err != nil || strings.HasPrefix(relPath, "..") {
		return "", fmt.Errorf("(zipslip) filepath is unsafe %q: %v", path2, err)
	}
	if path1 == "" {
		path1 = "."
	}
	return filepath.Join(path1, filepath.Join("/", relPath)), nil
}

// 获取文件 mime 类型, 参数的类型必须是 string 或者*os.File
func MiMeType(file any) string {
	var mediatype string

	readBuffer := func(f *os.File) ([]byte, error) {
		buffer := make([]byte, 512)
		_, err := f.Read(buffer)
		if err != nil {
			return nil, err
		}
		return buffer, nil
	}

	if filePath, ok := file.(string); ok {
		f, err := os.Open(filePath)
		if err != nil {
			return mediatype
		}
		buffer, err := readBuffer(f)
		if err != nil {
			return mediatype
		}
		return http.DetectContentType(buffer)
	}

	if f, ok := file.(*os.File); ok {
		buffer, err := readBuffer(f)
		if err != nil {
			return mediatype
		}
		return http.DetectContentType(buffer)
	}
	return mediatype
}

// 返回绝对路径
func CurrentPath() string {
	var absPath string
	_, filename, _, ok := runtime.Caller(1)
	if ok {
		absPath = path.Dir(filename)
	}

	return absPath
}

// 文件大小 字节
func FileSize(path string) (int64, error) {
	f, err := os.Stat(path)
	if err != nil {
		return 0, err
	}
	return f.Size(), nil
}

// FileCount
//
//	@Description: 文件格式化
//	@param sizes
//	@return string
func FileCount(sizes int64) string {
	a := [...]string{"B", "KB", "MB", "GB", "TB", "PB"}
	pos := 0
	s := float64(sizes)
	for s >= 1024 {
		s = s / 1024
		pos++
	}
	c := strconv.FormatFloat(s, 'f', 2, 64)
	return c + " " + a[pos]
}

// 文件修改时间戳
func MTime(filepath string) (int64, error) {
	f, err := os.Stat(filepath)
	if err != nil {
		return 0, err
	}
	return f.ModTime().Unix(), nil
}

// 读取csv
func ReadCsvFile(filepath string) ([][]string, error) {
	f, err := os.Open(filepath)
	if err != nil {
		return nil, err
	}
	defer f.Close()

	csvReader := csv.NewReader(f)
	records, err := csvReader.ReadAll()
	if err != nil {
		return nil, err
	}

	return records, nil
}

// 写入csv
func WriteCsvFile(filepath string, records [][]string, append bool) error {
	flag := os.O_RDWR | os.O_CREATE

	if append {
		flag = flag | os.O_APPEND
	}

	f, err := os.OpenFile(filepath, flag, 0644)
	if err != nil {
		return err
	}

	defer f.Close()

	writer := csv.NewWriter(f)
	writer.Comma = ','

	return writer.WriteAll(records)
}

// 写入文件字符
func WriteFile(filepath string, content string, append bool) error {
	var flag int
	if append {
		flag = os.O_RDWR | os.O_CREATE | os.O_APPEND
	} else {
		flag = os.O_RDWR | os.O_CREATE | os.O_TRUNC
	}

	f, err := os.OpenFile(filepath, flag, 0644)
	if err != nil {
		return err
	}
	defer f.Close()

	_, err = f.WriteString(content)
	return err
}

// 四舍五入到 float64 n位保留
func RoundToString(x float64, n int) string {
	tmp := math.Pow(10.0, float64(n))
	x *= tmp
	x = math.Round(x)
	result := strconv.FormatFloat(x/tmp, 'f', n, 64)
	return result
}

// 四舍五入到字符串
func RoundToFloat(x float64, n int) float64 {
	tmp := math.Pow(10.0, float64(n))
	x *= tmp
	x = math.Round(x)
	return x / tmp
}

// Sum[T Float | Integer | Complex]
//
//	@Description: 求和
//	@param collection
//	@return T
func Sum[T Float | Integer | Complex](collection []T) T {
	var sum T = 0
	for _, val := range collection {
		sum += val
	}
	return sum
}
func Max[T Ordered](collection []T) T {
	var max T

	if len(collection) == 0 {
		return max
	}

	max = collection[0]

	for i := 1; i < len(collection); i++ {
		item := collection[i]

		if item > max {
			max = item
		}
	}

	return max
}
func Min[T Ordered](collection []T) T {
	var min T

	if len(collection) == 0 {
		return min
	}

	min = collection[0]

	for i := 1; i < len(collection); i++ {
		item := collection[i]

		if item < min {
			min = item
		}
	}

	return min
}

// Range[T Integer | Float]
//
//	@Description: 生成数组
//	@param start Range(1,5)
//	@param elementNum
//	@return []T
func Range[T Integer | Float](start T, elementNum int) []T {
	var length int
	var step int
	if elementNum < 0 {
		length = -elementNum
	} else {
		length = elementNum
	}
	result := make([]T, length)
	if elementNum < 0 {
		step = -1
	} else {
		step = 1
	}
	for i, j := 0, start; i < length; i, j = i+1, j+T(step) {
		result[i] = j
	}
	return result
}

// 平均数
func Average[T Integer | Float](numbers ...T) T {
	var sum T
	n := T(len(numbers))

	for _, v := range numbers {
		sum += v
	}
	return sum / n
}

// 计算百分比
func Percent(val, total float64, n int) float64 {
	if total == 0 {
		return float64(0)
	}
	tmp := val / total * 100
	result := RoundToFloat(tmp, n)

	return result
}

// 截断小数n位 不四舍五入
func TruncRound(x float64, n int) float64 {
	floatStr := fmt.Sprintf("%."+strconv.Itoa(n+1)+"f", x)
	temp := strings.Split(floatStr, ".")
	var newFloat string
	if len(temp) < 2 || n >= len(temp[1]) {
		newFloat = floatStr
	} else {
		newFloat = temp[0] + "." + temp[1][:n]
	}
	result, _ := strconv.ParseFloat(newFloat, 64)
	return result
}

// 根据指定的起始值，结束值，步长，创建一个数字切片
func RangeWithStep[T Integer | Float](start, end, step T) []T {
	result := []T{}

	if start >= end || step == 0 {
		return result
	}

	for i := start; i < end; i += step {
		result = append(result, i)
	}

	return result
}

// 计算两坐标点距离
func PointDistance(x1, y1, x2, y2 float64) float64 {
	a := x1 - x2
	b := y1 - y2
	c := math.Pow(a, 2) + math.Pow(b, 2)

	return math.Sqrt(c)
}

// 下载文件
func DownloadFile(filepath string, url string) error {
	resp, err := http.Get(url)
	if err != nil {
		return err
	}
	defer resp.Body.Close()

	out, err := os.Create(filepath)
	if err != nil {
		return err
	}
	defer out.Close()

	_, err = io.Copy(out, resp.Body)

	return err
}

// 随机一个值
func RandInt(min, max int) int {
	if min == max {
		return min
	}
	if max < min {
		min, max = max, min
	}
	return rand.Intn(max-min) + min
}

/**
 * @Description: 四舍五入,分割字符
 * @param number 浮点数
 * @param decimals 保留位数2
 * @param decPoint .
 * @param thousandsSep , 分隔符
 * @return string
 */
func NumberFormat(number float64, decimals int, decPoint, thousandsSep string) string {
	neg := false
	if number < 0 {
		number = -number
		neg = true
	}
	dec := int(decimals)
	// Will round off
	str := fmt.Sprintf("%."+strconv.Itoa(dec)+"F", number)
	prefix, suffix := "", ""
	if dec > 0 {
		prefix = str[:len(str)-(dec+1)]
		suffix = str[len(str)-dec:]
	} else {
		prefix = str
	}
	sep := []byte(thousandsSep)
	n, l1, l2 := 0, len(prefix), len(sep)
	// thousands sep num
	c := (l1 - 1) / 3
	tmp := make([]byte, l2*c+l1)
	pos := len(tmp) - 1
	for i := l1 - 1; i >= 0; i, n, pos = i-1, n+1, pos-1 {
		if l2 > 0 && n > 0 && n%3 == 0 {
			for j := range sep {
				tmp[pos] = sep[l2-j-1]
				pos--
			}
		}
		tmp[pos] = prefix[i]
	}
	s := string(tmp)
	if dec > 0 {
		s += decPoint + suffix
	}
	if neg {
		s = "-" + s
	}

	return s
}
func UUIdV4() (string, error) {
	uuid := make([]byte, 16)

	n, err := io.ReadFull(crand.Reader, uuid)
	if n != len(uuid) || err != nil {
		return "", err
	}

	uuid[8] = uuid[8]&^0xc0 | 0x80
	uuid[6] = uuid[6]&^0xf0 | 0x40

	return fmt.Sprintf("%x-%x-%x-%x-%x", uuid[0:4], uuid[4:6], uuid[6:8], uuid[8:10], uuid[10:]), nil
}
func IsWindows() bool {
	return runtime.GOOS == "windows"
}
func IsLinux() bool {
	return runtime.GOOS == "linux"
}
func IsMac() bool {
	return runtime.GOOS == "darwin"
}

// 获取当前操作系统位数(32/64)
func GetOsBits() int {
	return 32 << (^uint(0) >> 63)
}
func IsASCII(str string) bool {
	for i := 0; i < len(str); i++ {
		if str[i] > unicode.MaxASCII {
			return false
		}
	}
	return true
}
func IsJSON(str string) bool {
	var js json.RawMessage
	return json.Unmarshal([]byte(str), &js) == nil
}
func IsIp(ipstr string) bool {
	ip := net.ParseIP(ipstr)
	return ip != nil
}
func IsUrl(str string) bool {
	if str == "" || len(str) >= 2083 || len(str) <= 3 || strings.HasPrefix(str, ".") {
		return false
	}
	u, err := url.Parse(str)
	if err != nil {
		return false
	}
	if strings.HasPrefix(u.Host, ".") {
		return false
	}
	if u.Host == "" && (u.Path != "" && !strings.Contains(u.Path, ".")) {
		return false
	}
	var urlMatcher *regexp.Regexp = regexp.MustCompile(`^((ftp|http|https?):\/\/)?(\S+(:\S*)?@)?((([1-9]\d?|1\d\d|2[01]\d|22[0-3])(\.(1?\d{1,2}|2[0-4]\d|25[0-5])){2}(?:\.([0-9]\d?|1\d\d|2[0-4]\d|25[0-4]))|(([a-zA-Z0-9]+([-\.][a-zA-Z0-9]+)*)|((www\.)?))?(([a-z\x{00a1}-\x{ffff}0-9]+-?-?)*[a-z\x{00a1}-\x{ffff}0-9]+)(?:\.([a-z\x{00a1}-\x{ffff}]{2,}))?))(:(\d{1,5}))?((\/|\?|#)[^\s]*)?$`)
	return urlMatcher.MatchString(str)
}
func IsEmail(email string) bool {
	var emailMatcher *regexp.Regexp = regexp.MustCompile(`\w+([-+.]\w+)*@\w+([-.]\w+)*\.\w+([-.]\w+)*`)
	return emailMatcher.MatchString(email)
}

// 是否手机号
func IsMobile(mobileNum string) bool {
	var chineseMobileMatcher *regexp.Regexp = regexp.MustCompile(`^1(?:3\d|4[4-9]|5[0-35-9]|6[67]|7[013-8]|8\d|9\d)\d{8}$`)
	return chineseMobileMatcher.MatchString(mobileNum)
}

// 是否身份证
func IsChineseIdNum(id string) bool {
	var chineseIdMatcher *regexp.Regexp = regexp.MustCompile(`^[1-9]\d{5}(18|19|20|21|22)\d{2}((0[1-9])|(1[0-2]))(([0-2][1-9])|10|20|30|31)\d{3}[0-9Xx]$`)
	return chineseIdMatcher.MatchString(id)
}

func IsChinese(s string) bool {
	var chineseMatcher *regexp.Regexp = regexp.MustCompile("[\u4e00-\u9fa5]")
	return chineseMatcher.MatchString(s)
}
func IsBase64(base64 string) bool {
	var base64Matcher *regexp.Regexp = regexp.MustCompile(`^(?:[A-Za-z0-9+\\/]{4})*(?:[A-Za-z0-9+\\/]{2}==|[A-Za-z0-9+\\/]{3}=|[A-Za-z0-9+\\/]{4})$`)
	return base64Matcher.MatchString(base64)
}

// 验证字符串是否是强密码：（字母+数字+特殊字符)
func IsStrongPassword(password string, length int) bool {
	if len(password) < length {
		return false
	}
	var num, lower, upper, special bool
	for _, r := range password {
		switch {
		case unicode.IsDigit(r):
			num = true
		case unicode.IsUpper(r):
			upper = true
		case unicode.IsLower(r):
			lower = true
		case unicode.IsSymbol(r), unicode.IsPunct(r):
			special = true
		}
	}

	return num && lower && upper && special
}
func IsGBK(data []byte) bool {
	i := 0
	for i < len(data) {
		if data[i] <= 0xff {
			i++
			continue
		} else {
			if data[i] >= 0x81 &&
				data[i] <= 0xfe &&
				data[i+1] >= 0x40 &&
				data[i+1] <= 0xfe &&
				data[i+1] != 0xf7 {
				i += 2
				continue
			} else {
				return false
			}
		}
	}

	return true
}
func IsUtf8(s string) bool {
	return utf8.ValidString(s)
}
func IsWeixin(r *http.Request) bool {
	if strings.Index(r.UserAgent(), "icroMessenger") == -1 {
		return false
	} else {
		return true
	}
}

// 是否是数字
func IsNumber(v any) bool {
	return IsInt(v) || IsFloat(v)
}

// 是否浮点
func IsFloat(v any) bool {
	switch v.(type) {
	case float32, float64:
		return true
	}
	return false
}

// 是否整数
func IsInt(v any) bool {
	switch v.(type) {
	case int, int8, int16, int32, int64, uint, uint8, uint16, uint32, uint64, uintptr:
		return true
	}
	return false
}

// 判断是否周日
func IsWeekend(t time.Time) bool {
	return time.Saturday == t.Weekday() || time.Sunday == t.Weekday()
}

// 是否闰年
func IsLeapYear(year int) bool {
	return year%4 == 0 && (year%100 != 0 || year%400 == 0)
}

// 数据类型获取
func Typeof(a any) reflect.Type {
	return reflect.TypeOf(a)
}

// 时间戳
func Time() int64 {
	return time.Now().Unix()
}

// Date
//
//	@Description: 格式化时间
//	@param format Y-m-d H:i:s
//	@param ts 事件类型
//	@return string
func Date(format string, ts ...time.Time) string {
	patterns := []string{
		// 年
		"Y", "2006", // 4 位数字完整表示的年份
		"y", "06", // 2 位数字表示的年份

		// 月
		"m", "01", // 数字表示的月份，有前导零
		"n", "1", // 数字表示的月份，没有前导零
		"M", "Jan", // 三个字母缩写表示的月份
		"F", "January", // 月份，完整的文本格式，例如 January 或者 March

		// 日
		"d", "02", // 月份中的第几天，有前导零的 2 位数字
		"j", "2", // 月份中的第几天，没有前导零

		"D", "Mon", // 星期几，文本表示，3 个字母
		"l", "Monday", // 星期几，完整的文本格式;L的小写字母

		// 时间
		"g", "3", // 小时，12 小时格式，没有前导零
		"G", "15", // 小时，24 小时格式，没有前导零
		"h", "03", // 小时，12 小时格式，有前导零
		"H", "15", // 小时，24 小时格式，有前导零

		"a", "pm", // 小写的上午和下午值
		"A", "PM", // 小写的上午和下午值

		"i", "04", // 有前导零的分钟数
		"s", "05", // 秒数，有前导零
	}
	replacer := strings.NewReplacer(patterns...)
	format = replacer.Replace(format)

	t := time.Now()
	if len(ts) > 0 {
		t = ts[0]
	}
	return t.Format(format)
}

// Timestr2Time
//
//	@Description: 时间字符串转换时间类;
//	@param str
//	@return time.Time
func Timestr2Time(str string) time.Time {
	const Layout = "2006-01-02 15:04:05" //时间常量
	loc, _ := time.LoadLocation("Asia/Shanghai")
	times, _ := time.ParseInLocation(Layout, str, loc)
	return times
}

// Unix2Time
//
//	@Description: 时间戳转换时间类型
//	@param t
//	@return time.Time
func Unix2Time(t int64) time.Time {
	const timeLayout = "2006-01-02 15:04:05"
	str := time.Unix(t, 0).Format(timeLayout)
	return Timestr2Time(str)
}

// Str2Time
//
//	@Description: 时间字符串转换时间戳
//	@param s
//	@return int64
func Str2Time(s string) int64 {
	const timeLayout = "2006-01-02 15:04:05"
	loc, _ := time.LoadLocation("Local")
	tmp, _ := time.ParseInLocation(timeLayout, s, loc)
	timestamp := tmp.Unix()
	return timestamp
}

// TimeLine
//
//	@Description: 时间友好显示
//	@param t 时间戳
//	@return string
func TimeLine(t int64) string {
	now := time.Now().Unix()
	var xx string
	if now <= t {
		xx = Date("Y-m-d H:i:s", Unix2Time(t))
	} else {
		t = now - t
		f := map[int]string{
			31536000: "年",
			2592000:  "个月",
			604800:   "星期",
			86400:    "天",
			3600:     "小时",
			60:       "分钟",
			1:        "秒"}
		var keys []int
		for k := range f {
			keys = append(keys, k)
		}
		sort.Sort(sort.Reverse(sort.IntSlice(keys)))
		for _, v := range keys {
			k1 := int64(v)
			x := t / k1
			if x != 0 {
				x1 := strconv.FormatInt(x, 10)
				xx = x1 + f[v] + "前"
				break
			}
		}
	}
	return xx
}

/**
 * @Description: 返回当前 Unix 时间戳和微秒数
 * @return float64
 */
func MicroTime() float64 {
	loc, _ := time.LoadLocation("UTC")
	now := time.Now().In(loc)
	micSeconds := float64(now.Nanosecond()) / 1000000000
	return float64(now.Unix()) + micSeconds
}

// 根据年月日判断星期 2021-03-17
func GetWeekday(ri string) string {
	var weekday = [7]string{"周日", "周一", "周二", "周三", "周四", "周五", "周六"}
	t := Timestr2Time(ri + " 00:00:00")
	n := int(t.Weekday())
	return weekday[n]
}

// 获取exe路径
func GetAppPath() string {
	file, _ := exec.LookPath(os.Args[0])
	path, _ := filepath.Abs(file)
	index := strings.LastIndex(path, string(os.PathSeparator))
	return path[:index]
}

// Uniqid
//
//	@Description: 生成随机字符串
//	@param prefix 前缀
//	@return string
func Uniqid(prefix string) string {
	now := time.Now()
	return fmt.Sprintf("%s%08x%05x", prefix, now.Unix(), now.UnixNano()%0x100000)
}

/**
 * @Description: 创建密码散列,password 密码
 * @param password 要加密字符串
 * @return string
 * @return error
 */
func PasswordHash(password string) (string, error) {
	salt, _ := Salt(10)
	hash, err := Hash(password, salt)
	return hash, err
}

/**
 * @Description: 验证密码,密码和密码散列
 * @param password 密码
 * @param hash 上面生成的散列密码
 * @return bool
 */
func PasswordVerify(password, hash string) bool {
	is := Match(password, hash)
	return is
}

/**
 * @Description: 去除字符中HTML标记
 * @param content 字符串
 * @return string
 */
func StripTags(content string) string {
	re := regexp.MustCompile(`<(.|\n)*?>`)
	return re.ReplaceAllString(content, "")
}

// 显示错误
func Err(err error) {
	if err != nil {
		panic(err)
	}
}

/**
 * @Description: cli实现提示输入 qq:=php.Ask("请输入",nil)
 * @param str 提示字符串
 * @param check nil
 * @return string
 */
func Ask(str string, check func(string) error) string {
	if check == nil {
		check = func(in string) error {
			if len(in) > 0 {
				return nil
			} else {
				return fmt.Errorf("Cannot be empty")
			}
		}
	}
	input := bufio.NewReader(os.Stdin)
	for {
		fmt.Printf(str + "")
		line, _, err := input.ReadLine()
		for err == io.EOF {
			<-time.After(time.Millisecond)
			line, _, err = input.ReadLine()
		}
		if err != nil {
			fmt.Printf("<warn>%s \n\n", err)
		} else if err = check(string(line)); err != nil {
			fmt.Printf("<warn>%s \n\n", err)
		} else {
			return string(line)
		}
	}
}

// cli选择
var RenderChooseQuestion = func(question string) string {
	return question + "\n"
}
var RenderChooseOption = func(key, value string, size int) string {
	return fmt.Sprintf("%-"+fmt.Sprintf("%d", size+1)+"s %s\n", key+")", value)
}
var RenderChooseQuery = func() string {
	return "Choose: "
}

/*
*
  - @Description: cli选择
  - @param question 提示内容
  - @param choices  map[string]string{
    "1":  "苹果",
    "2": "橘子",
    "3":   "西瓜",
    }
  - @return string 返回key
*/
func Choose(question string, choices map[string]string) string {
	options := RenderChooseQuestion(question)
	keys := []string{}
	max := 0
	for k, _ := range choices {
		if l := len(k); l > max {
			max = l
		}
		keys = append(keys, k)
	}
	sort.Strings(keys)
	for _, k := range keys {
		options += RenderChooseOption(k, choices[k], max)
	}
	options += RenderChooseQuery()
	return Ask(options, func(in string) error {
		if _, ok := choices[in]; ok {
			return nil
		} else {
			return fmt.Errorf("Choose one of: %s", strings.Join(keys, ", "))
		}
	})
}

var ConfirmRejection = "<warn>Please respond with \"y\" or \"n\"\n\n"
var ConfirmYesRegex = regexp.MustCompile(`^(?i)y(es)?$`)
var ConfirmNoRegex = regexp.MustCompile(`^(?i)no?$`)

/**
 * @Description: cli选择yes/no
 * @param question 提示内容支持回复 yes y/no n
 * @return bool
 */
func Confirm(question string) bool {
	cb := func(value string) error { return nil }
	for {
		res := Ask(question, cb)
		if ConfirmYesRegex.MatchString(res) {
			return true
		} else if ConfirmNoRegex.MatchString(res) {
			return false
		} else {
			fmt.Printf(ConfirmRejection)
		}
	}
}

// Map2Http
//
//	@Description: map转换成http字符串
//	@param param map 转换成a=1&b=2&c=3
//	@return string
func Map2Http(param map[string]any) string {
	if param == nil {
		return ""
	}
	var keys []string
	for key := range param {
		keys = append(keys, key)
	}
	sort.Strings(keys)

	var build strings.Builder
	for i, v := range keys {
		build.WriteString(v)
		build.WriteString("=")
		build.WriteString(fmt.Sprintf("%v", param[v]))
		if i != len(keys)-1 {
			build.WriteString("&")
		}
	}
	return build.String()
}

// GetIp
//
//	@Description: 获取IP
//	@return string
func GetIp() string {
	addr, err := net.InterfaceAddrs()
	if err != nil {
		panic(err.Error())
	}
	for _, a := range addr {
		if ipNet, ok := a.(*net.IPNet); ok && !ipNet.IP.IsLoopback() {
			if ipNet.IP.To4() != nil {
				return ipNet.IP.String()
			}
		}
	}

	return ""
}

// 编码URL
func EncodeUrl(urlStr string) (string, error) {
	URL, err := url.Parse(urlStr)
	if err != nil {
		return "", err
	}

	URL.RawQuery = URL.Query().Encode()

	return URL.String(), nil
}

// 访问url
func Openurl(url string) {
	var cmd string
	var args []string

	switch runtime.GOOS {
	case "windows":
		cmd = "cmd"
		args = []string{"/c", "start"}
	case "darwin":
		cmd = "open"
	default:
		cmd = "xdg-open"
	}
	args = append(args, url)
	cmds := exec.Command(cmd, args...)
	cmds.Start()
}

/*
*
  - @Description: 发送邮件不使用任何扩展
    from :="logwwwove@qq.com"
    to1:="yobybxy@163.com,18291448834@163.com"
    secret := "abc"
    host :="smtp.qq.com"
    port := 25
    subject:="主题"
    body:="内容是测试"
    err:=php.SendEmail(from,to1,subject,body,secret,host,port)
    php.CheckErr(err)
  - @param from 发送人邮箱
  - @param to1 收件人邮箱,多个用,隔开"yoby21bxy@163.com,182914114811834@163.com"
  - @param subject 标题
  - @param body 内容
  - @param secret 密钥,qq邮箱授权码密码
  - @param host 主机地址
  - @param port 端口25
  - @return err
*/
func SendEmail(from string, to1 string, subject string, body string, secret string, host string, port int) (err error) {
	to2 := strings.Split(to1, ",")
	to := to2[0]
	auth := smtp.PlainAuth("", from, secret, host)
	msg := []byte("To: " + to + "\r\n" +
		"Subject: " + subject + "\r\n" +
		"\r\n" +
		body + "\r\n")
	err = smtp.SendMail(host+":"+strconv.Itoa(port), auth, from, to2, msg)
	return err
}

/**
 * @Description: 解码emoji网页上显示
 * @param s
 * @return string
 */
func EmojiDecode(s string) string {
	re := regexp.MustCompile("\\[[\\\\u0-9a-zA-Z]+\\]")
	//提取emoji数据表达式
	reg := regexp.MustCompile("\\[\\\\u|]")
	src := re.FindAllString(s, -1)
	for i := 0; i < len(src); i++ {
		e := reg.ReplaceAllString(src[i], "")
		p, err := strconv.ParseInt(e, 16, 32)
		if err == nil {
			s = strings.Replace(s, src[i], string(rune(p)), -1)
		}
	}
	return s
}

/**
 * @Description: 编码emoji成unicode
 * @param s
 * @return string
 */
func EmojiEncode(s string) string {
	ret := ""
	rs := []rune(s)
	for i := 0; i < len(rs); i++ {
		if len(string(rs[i])) == 4 {
			u := `[\u` + strconv.FormatInt(int64(rs[i]), 16) + `]`
			ret += u

		} else {
			ret += string(rs[i])
		}
	}
	return ret
}

/**
 * @Description: emoji编码成实体直接输出不需要转码
 * @param s
 * @return ss
 */
func Emoji(s string) (ss string) {
	s1 := strings.Split(s, "")
	for _, v := range s1 {
		if len(v) >= 4 {
			vv := []rune(v)
			k := int(vv[0])
			ss += "&#" + strconv.Itoa(k) + ";"
		} else {
			ss += v
		}
	}
	return
}

// 字符串截取 字符串 位置 长度
func Substring(s string, offset int, length uint) string {
	rs := []rune(s)
	size := len(rs)

	if offset < 0 {
		offset = size + offset
		if offset < 0 {
			offset = 0
		}
	}
	if offset > size {
		return ""
	}

	if length > uint(size)-uint(offset) {
		length = uint(size - offset)
	}

	str := string(rs[offset : offset+int(length)])

	return strings.Replace(str, "\x00", "", -1)
}

/*
*
  - @Description: 对称加密解密函数
  - @param text 要加密或解密字符串
  - @param false解码 true加密

密钥 字符串
s:=php.Authcode("1234==+wo我们",true,"abc")
s=php.Authcode(s,false,"abc")
  - @return string
*/
func Authcode(text string, params ...interface{}) string {
	l := len(params)

	isEncode := false
	key := ""
	expiry := 0
	cKeyLen := 4

	if l > 0 {
		isEncode = params[0].(bool)
	}

	if l > 1 {
		key = params[1].(string)
	}

	if l > 2 {
		expiry = params[2].(int)
		if expiry < 0 {
			expiry = 0
		}
	}

	if l > 3 {
		cKeyLen = params[3].(int)
		if cKeyLen < 0 {
			cKeyLen = 0
		}
	}
	if cKeyLen > 32 {
		cKeyLen = 32
	}

	timestamp := time.Now().Unix()

	// md5加密key
	mKey := Md5(key)

	// 参与加密的
	keyA := Md5(mKey[0:16])
	// 用于验证数据有效性的
	keyB := Md5(mKey[16:])
	// 动态部分
	var keyC string
	if cKeyLen > 0 {
		if isEncode {
			// 加密的时候，动态获取一个秘钥
			keyC = Md5(fmt.Sprint(timestamp))[32-cKeyLen:]
		} else {
			// 解密的时候从头部获取动态秘钥部分
			keyC = text[0:cKeyLen]
		}
	}

	// 加入了动态的秘钥
	cryptKey := keyA + Md5(keyA+keyC)
	// 秘钥长度
	keyLen := len(cryptKey)
	if isEncode {
		// 加密 前10位是过期验证字符串 10-26位字符串验证
		var d int64
		if expiry > 0 {
			d = timestamp + int64(expiry)
		}
		text = fmt.Sprintf("%010d%s%s", d, Md5(text + keyB)[0:16], text)
	} else {
		// 解密
		text = string(Base64Decode(text[cKeyLen:], false))
	}

	// 字符串长度
	textLen := len(text)
	if textLen <= 0 {
		return ""
	}

	// 密匙簿
	box := Range(0, 256)

	// 对称算法
	var rndKey []int
	cryptKeyB := []byte(cryptKey)
	for i := 0; i < 256; i++ {
		pos := i % keyLen
		rndKey = append(rndKey, int(cryptKeyB[pos]))
	}

	j := 0
	for i := 0; i < 256; i++ {
		j = (j + box[i] + rndKey[i]) % 256
		box[i], box[j] = box[j], box[i]
	}

	textB := []byte(text)
	a := 0
	j = 0
	var result []byte
	for i := 0; i < textLen; i++ {
		a = (a + 1) % 256
		j = (j + box[a]) % 256
		box[a], box[j] = box[j], box[a]
		result = append(result, byte(int(textB[i])^(box[(box[a]+box[j])%256])))
	}

	if isEncode {
		return keyC + strings.Replace(Base64Encode(string(result), false), "=", "", -1)
	}

	// 获取前10位，判断过期时间
	d, _ := strconv.ParseInt(string(result[0:10]), 10, 0)
	if (d == 0 || d-timestamp > 0) && string(result[10:26]) == Md5(string(result[26:]) + keyB)[0:16] {
		return string(result[26:])
	}

	return ""
}

/*
*
  - @Description: 图片转换成base64

filename:="1.jpg"
s:=php.Img2Base64(filename)
  - @param filename
  - @return s
*/
func Img2Base64(filename string) (s string) {
	ext := filepath.Ext(filename)
	ext = strings.TrimLeft(ext, ".")
	srcByte, _ := os.ReadFile(filename)
	s = Base64Encode(string(srcByte), false)
	s = "data:image/" + ext + ";base64," + s
	return
}

/**
 * @Description: base64还原成图片
 * @param path 当前 . qq/ss 最后不要带/
 * @param data 上传的base64
 * @return ps 路径
 */
func Base642Img(path, data string) (ps string) {
	re := regexp.MustCompile(`^(data:\s*image\/(\w+);base64,)`)
	r := re.FindStringSubmatch(data)
	ext := r[2]
	bs := strings.Replace(data, r[1], "", -1)
	CreateDir(path)
	ps = path + "/" + Sha1(data) + "." + ext
	bs = Base64Decode(bs, false)
	os.WriteFile(ps, []byte(bs), 0666)
	return ps
}

/**
 * @Description: 生成随机颜色
 * @return string
 */
func RandColor() string {
	str := "abcdef0123456789"
	var s string
	for i := 0; i < 6; i++ {
		n := RandInt(0, 15)
		time.Sleep(1)
		s += Substring(str, n, 1)
	}
	return "#" + s
}

/**
 * @Description: html字符串转换实体
 * @param s
 * @return string
 */
func HtmlEncode(s string) string {
	return html.EscapeString(s)
}

/**
 * @Description: html实体字符串还原
 * @param s
 * @return string
 */
func HtmlDecode(s string) string {
	return html.UnescapeString(s)
}

/**
 * @Description: GET请求,支持gzip
 * @param u 网址
 * @return string
 */
func Get(u string) string {
	rs, _ := http.Get(u)
	defer rs.Body.Close()
	body, _ := io.ReadAll(rs.Body)
	t := string(body)
	if IsGBK(body) {
		return Gbk2Utf8(t)
	}
	return t
}

// table转换成数组
func TableArr(s string) [][]string {
	re := regexp.MustCompile("<table[^>]*?>")
	s = re.ReplaceAllString(s, "")
	re = regexp.MustCompile("<tbody[^>]*?>")
	s = re.ReplaceAllString(s, "")
	re = regexp.MustCompile("<tr[^>]*?>")
	s = re.ReplaceAllString(s, "")
	re = regexp.MustCompile("<td[^>]*?>")
	s = re.ReplaceAllString(s, "")
	s = strings.Replace(s, "</tr>", "{tr}", -1)
	s = strings.Replace(s, "</td>", "{td}", -1)
	re = regexp.MustCompile("<[/!]*?[^<>]*?>")
	s = re.ReplaceAllString(s, "")
	re = regexp.MustCompile("([rn])[s]+")
	s = re.ReplaceAllString(s, "")
	re = regexp.MustCompile("&nbsp;")
	s = re.ReplaceAllString(s, "")
	re = regexp.MustCompile("</tbody>")
	s = re.ReplaceAllString(s, "")
	re = regexp.MustCompile("</table>")
	s = re.ReplaceAllString(s, "")
	re = regexp.MustCompile(`\s{2,}`)
	s = re.ReplaceAllString(s, "")
	s = strings.Replace(s, " ", "", -1)
	s = strings.Replace(s, "	", "", -1)
	s = strings.Replace(s, "\r", "", -1)
	s = strings.Replace(s, "\t", "", -1)
	s = strings.Replace(s, "\n", "", -1)
	arr := strings.Split(s, "{tr}")
	arr = arr[:len(arr)-1]
	var arr1 [][]string
	for _, v := range arr {
		arr2 := strings.Split(v, "{td}")
		arr2 = arr2[:len(arr2)-1]
		arr1 = append(arr1, arr2)
	}
	return arr1
}

var aes128 = []byte{0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f}
var aes192 = []byte{0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
	0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
}
var aes256 = []byte{0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
	0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
}

/**
 * @Description: Aes加密
 * @param text
 * @param key ,分别代表AES-128, AES-192和 AES-256
 * @return string
 * @return error
 */
func AesEn(text string, k string) (string, error) {
	var key []byte
	switch k {
	case "aes128":
		key = aes128
	case "aes192":
		key = aes192
	case "aes256":
		key = aes256
	}
	var iv = key[:aes.BlockSize]
	encrypted := make([]byte, len(text))
	block, err := aes.NewCipher(key)
	if err != nil {
		return "", err
	}
	encrypter := cipher.NewCFBEncrypter(block, iv)
	encrypter.XORKeyStream(encrypted, []byte(text))
	return hex.EncodeToString(encrypted), nil
}

// aes解密 支持aes128 aes192 aes256
func AesDe(encrypted string, k string) (string, error) {
	var key []byte
	switch k {
	case "aes128":
		key = aes128
	case "aes192":
		key = aes192
	case "aes256":
		key = aes256
	}
	var err error
	defer func() {
		if e := recover(); e != nil {
			err = e.(error)
		}
	}()
	src, err := hex.DecodeString(encrypted)
	if err != nil {
		return "", err
	}
	var iv = key[:aes.BlockSize]
	decrypted := make([]byte, len(src))
	var block cipher.Block
	block, err = aes.NewCipher([]byte(key))
	if err != nil {
		return "", err
	}
	decrypter := cipher.NewCFBDecrypter(block, iv)
	decrypter.XORKeyStream(decrypted, src)
	return string(decrypted), nil
}

var (
	// DefaultTrimChars are the characters which are stripped by Trim* functions in default.
	DefaultTrimChars = string([]byte{
		'\t', // Tab.
		'\v', // Vertical tab.
		'\n', // New line (line feed).
		'\r', // Carriage return.
		'\f', // New page.
		' ',  // Ordinary space.
		0x00, // NUL-byte.
		0x85, // Delete.
		0xA0, // Non-breaking space.
	})
)

// 开头结尾去除空格或指定字符
func Trim(str string, characterMask ...string) string {
	trimChars := DefaultTrimChars

	if len(characterMask) > 0 {
		trimChars += characterMask[0]
	}

	return strings.Trim(str, trimChars)
}

// SplitStr
//
//	@Description: 切割字符串为scile
//	@param str
//	@param delimiter 切割符号
//	@param characterMask 去除空格或其他
//	@return []string
func SplitStr(str, delimiter string, characterMask ...string) []string {
	result := make([]string, 0)

	for _, v := range strings.Split(str, delimiter) {
		v = Trim(v, characterMask...)
		if v != "" {
			result = append(result, v)
		}
	}

	return result
}

// HideString
//
//	@Description: 隐藏字符串特定位置
//	@param origin
//	@param start
//	@param end
//	@param replaceChar
//	@return string
func HideString(origin string, start, end int, replaceChar string) string {
	size := len(origin)

	if start > size-1 || start < 0 || end < 0 || start > end {
		return origin
	}

	if end > size {
		end = size
	}

	if replaceChar == "" {
		return origin
	}

	startStr := origin[0:start]
	endStr := origin[end:size]

	replaceSize := end - start
	replaceStr := strings.Repeat(replaceChar, replaceSize)

	return startStr + replaceStr + endStr
}

/**
 * @Description: 隐藏手机中间四位或电话中间四位
 * @param phone 手机号 182XXXX7788
 * @return str
 */
func HideTel(phone string) (str string) {
	return HideString(phone, 3, 7, "*")
}

// 获取汉字拼音,支持返回全拼音和拼音首字母,同时支持sp分隔符 php.GetPinyin(s,"")
func GetPinyin(s, sp string) (pinyin, shortpinyin string) {
	n := utf8.RuneCountInString(s)
	var list []string
	for i := 0; i < n; i++ {
		list = append(list, Substring(s, i, 1))
	}
	for _, v := range list {
		pin, isok := dict[v]
		if isok {
			pinyin += pin + sp
			shortpinyin += Substring(pin, 0, 1)
		} else {
			pinyin += v
			shortpinyin += Substring(v, 0, 1)
		}

	}
	return pinyin, shortpinyin
}

// utf82unicode
// @Description: utf8转换unnicode
// @param str
// @return string unicode
func Utf82unicode(str string) string {
	str1 := strconv.QuoteToASCII(str)
	return str1[1 : len(str1)-1]
}

// unicode2utf8
// @Description: unicode转换utf8
// @param str
// @return string utf8
func Unicode2utf8(str string) string {
	str1, _ := strconv.Unquote(strings.Replace(strconv.Quote(str), `\\u`, `\u`, -1))
	return str1
}
