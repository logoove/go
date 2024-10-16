package yo

import (
	"archive/zip"
	"bufio"
	"bytes"
	"crypto/aes"
	"crypto/cipher"
	"crypto/md5"
	"crypto/sha1"
	"crypto/sha256"
	"crypto/sha512"
	"encoding/base64"
	"encoding/binary"
	"encoding/csv"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"math"
	"math/rand/v2"
	"net"
	"net/http"
	"net/mail"
	"net/url"
	"os"
	"os/exec"
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
	~int | ~int8 | ~int16 | ~int32 | ~int64 |
		~uint | ~uint8 | ~uint16 | ~uint32 | ~uint64 | ~uintptr |
		~float32 | ~float64 |
		~string
}
type Entry[K comparable, V any] struct {
	Key   K
	Value V
}
type Map = map[string]any
type MapStrStr = map[string]string
type MapStrInt = map[string]int
type MapIntStr = map[int]string
type MapIntInt = map[int]int
type MapStrAny = map[string]any
type MapIntAny = map[int]any

var timeFormat = MapStrStr{
	"yyyy-mm-dd hh:mm:ss": "2006-01-02 15:04:05",
	"yyyy-mm-dd hh:mm":    "2006-01-02 15:04",
	"yyyy-mm-dd hh":       "2006-01-02 15",
	"yyyy-mm-dd":          "2006-01-02",
	"yyyy-mm":             "2006-01",
	"mm-dd":               "01-02",
	"dd-mm-yy hh:mm:ss":   "02-01-06 15:04:05",
	"yyyy/mm/dd hh:mm:ss": "2006/01/02 15:04:05",
	"yyyy/mm/dd hh:mm":    "2006/01/02 15:04",
	"yyyy/mm/dd hh":       "2006/01/02 15",
	"yyyy/mm/dd":          "2006/01/02",
	"yyyy/mm":             "2006/01",
	"mm/dd":               "01/02",
	"dd/mm/yy hh:mm:ss":   "02/01/06 15:04:05",
	"yyyymmdd":            "20060102",
	"mmddyy":              "010206",
	"yyyy":                "2006",
	"yy":                  "06",
	"mm":                  "01",
	"hh:mm:ss":            "15:04:05",
	"hh:mm":               "15:04",
	"mm:ss":               "04:05",
}
var (
	factor = [17]int{7, 9, 10, 5, 8, 4, 2, 1, 6, 3, 7, 9, 10, 5, 8, 4, 2}
	verifyStr = [11]string{"1", "0", "X", "9", "8", "7", "6", "5", "4", "3", "2"}
	birthStartYear = 1900
provinceKv = map[string]struct{}{ "11": {}, "12": {}, "13": {}, "14": {}, "15": {}, "21": {}, "22": {}, "23": {}, "31": {}, "32": {}, "33": {}, "34": {}, "35": {}, "36": {}, "37": {}, "41": {}, "42": {}, "43": {}, "44": {}, "45": {}, "46": {}, "50": {}, "51": {}, "52": {}, "53": {}, "54": {}, "61": {}, "62": {}, "63": {}, "64": {}, "65": {}, "71": {}, "81": {}, "82": {}, } )
var (
	chineseMatcher       *regexp.Regexp = regexp.MustCompile("[\u4e00-\u9fa5]")
	base64Matcher        *regexp.Regexp = regexp.MustCompile(`^(?:[A-Za-z0-9+\\/]{4})*(?:[A-Za-z0-9+\\/]{2}==|[A-Za-z0-9+\\/]{3}=|[A-Za-z0-9+\\/]{4})$`)
	chineseMobileMatcher *regexp.Regexp = regexp.MustCompile(`^1(?:3\d|4[4-9]|5[0-35-9]|6[67]|7[013-8]|8\d|9\d)\d{8}$`)
	chineseIdMatcher     *regexp.Regexp = regexp.MustCompile(`^(\d{17})([0-9]|X|x)$`)
	creditCardMatcher    *regexp.Regexp = regexp.MustCompile(`^(?:4[0-9]{12}(?:[0-9]{3})?|5[1-5][0-9]{14}|(222[1-9]|22[3-9][0-9]|2[3-6][0-9]{2}|27[01][0-9]|2720)[0-9]{12}|6(?:011|5[0-9][0-9])[0-9]{12}|3[47][0-9]{13}|3(?:0[0-5]|[68][0-9])[0-9]{11}|(?:2131|1800|35\\d{3})\\d{11}|6[27][0-9]{14})$`)
	base64URLMatcher     *regexp.Regexp = regexp.MustCompile(`^([A-Za-z0-9_-]{4})*([A-Za-z0-9_-]{2}(==)?|[A-Za-z0-9_-]{3}=?)?$`)
	hexMatcher           *regexp.Regexp = regexp.MustCompile(`^(#|0x|0X)?[0-9a-fA-F]+$`)
	urlMatcher           *regexp.Regexp = regexp.MustCompile(`^((ftp|http|https?):\/\/)?(\S+(:\S*)?@)?((([1-9]\d?|1\d\d|2[01]\d|22[0-3])(\.(1?\d{1,2}|2[0-4]\d|25[0-5])){2}(?:\.([0-9]\d?|1\d\d|2[0-4]\d|25[0-4]))|(([a-zA-Z0-9]+([-\.][a-zA-Z0-9]+)*)|((www\.)?))?(([a-z\x{00a1}-\x{ffff}0-9]+-?-?)*[a-z\x{00a1}-\x{ffff}0-9]+)(?:\.([a-z\x{00a1}-\x{ffff}]{2,}))?))(:(\d{1,5}))?((\/|\?|#)[^\s]*)?$`)
)
// Assign[K comparable, V any, Map ~map[K]V]
//
//	@Description: 合并map
//	@param maps
//	@return Map
func Assign[K comparable, V any, Map ~map[K]V](maps ...Map) Map {
	count := 0
	for i := range maps {
		count += len(maps[i])
	}

	out := make(Map, count)
	for i := range maps {
		for k := range maps[i] {
			out[k] = maps[i][k]
		}
	}

	return out
}
func humanateBytes(s uint64, base float64, sizes []string) string {
	if s < 10 {
		return fmt.Sprintf("%d B", s)
	}
	e := math.Floor(math.Log(float64(s)) / math.Log(base))
	suffix := sizes[int(e)]
	val := math.Floor(float64(s)/math.Pow(base, e)*10+0.5) / 10
	f := "%.0f %s"
	if val < 10 {
		f = "%.1f %s"
	}

	return fmt.Sprintf(f, val, suffix)
}

var aes128 = []byte{0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f}
var aes192 = []byte{0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
	0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
}
var aes256 = []byte{0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
	0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
}

// AesEncode
//
//	@Description: AES加密,支持aes128 192 256
//	@param text
//	@param k
//	@return string
//	@return error
func AesEncode(text string, k string) (string, error) {
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

// AesDecode
//
//	@Description: AES解密
//	@param encrypted
//	@param k
//	@return string
//	@return error
func AesDecode(encrypted string, k string) (string, error) {
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

// AuthCode

// Authcode("1234==+wo我们",true,"abc")
//
//	@Description:对称加密解密
//	@param text
//	@param params
//	@return string
func AuthCode(text string, params ...interface{}) string {
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
		text = string(Base64Decode(text[cKeyLen:]))
	}

	// 字符串长度
	textLen := len(text)
	if textLen <= 0 {
		return ""
	}

	// 密匙簿
	box := Range(0, 256, 1)

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
		return keyC + strings.Replace(Base64Encode(string(result)), "=", "", -1)
	}

	// 获取前10位，判断过期时间
	d, _ := strconv.ParseInt(string(result[0:10]), 10, 0)
	if (d == 0 || d-timestamp > 0) && string(result[10:26]) == Md5(string(result[26:]) + keyB)[0:16] {
		return string(result[26:])
	}

	return ""
}

// ToBits
//
//	@Description: 字节格式化
//	@param s
//	@return string
func ToBits(s uint64) string {
	sizes := []string{"B", "kB", "MB", "GB", "TB", "PB", "EB"}
	return humanateBytes(s, 1000, sizes)
}

// Base64Encode
//
//	@Description: base64编码
//	@param s
//	@return string
func Base64Encode(s string) string {
	return base64.StdEncoding.EncodeToString([]byte(s))
}

// Base64Decode
//
//	@Description: base64解码
//	@param s
//	@return string
func Base64Decode(s string) string {
	b, _ := base64.StdEncoding.DecodeString(s)
	return string(b)
}

// Chunk[T any, Slice ~[]T]
//
//	@Description: 分割数组
//	@param collection
//	@param size
//	@return []Slice
func Chunk[T any, Slice ~[]T](collection Slice, size int) []Slice {
	if size <= 0 {
		panic("Second parameter must be greater than 0")
	}

	chunksNum := len(collection) / size
	if len(collection)%size != 0 {
		chunksNum += 1
	}

	result := make([]Slice, 0, chunksNum)

	for i := 0; i < chunksNum; i++ {
		last := (i + 1) * size
		if last > len(collection) {
			last = len(collection)
		}
		result = append(result, collection[i*size:last:last])
	}

	return result
}

// Compact[T comparable, Slice ~[]T]
//
//	@Description: 返回去除 "" nil字符的切片
//	@param collection
//	@return Slice
func Compact[T comparable, Slice ~[]T](collection Slice) Slice {
	var zero T

	result := make(Slice, 0, len(collection))

	for i := range collection {
		if collection[i] != zero {
			result = append(result, collection[i])
		}
	}

	return result
}

// CountBy[T any]
//
//	@Description: 计算符合条件元素数量
//	@param collection
//	@param predicate
//	@return count
func CountBy[T any](collection []T, predicate func(item T) bool) (count int) {
	for i := range collection {
		if predicate(collection[i]) {
			count++
		}
	}

	return count
}

// Contains[T comparable]
//
//	@Description: 数组中是否包含某元素
//	@param collection
//	@param element
//	@return bool
func Contains[T comparable](collection []T, element T) bool {
	for i := range collection {
		if collection[i] == element {
			return true
		}
	}

	return false
}

// CreateFile
//
//	@Description: 创建文件
//	@param path
//	@return bool
func CreateFile(path string) bool {
	file, err := os.Create(path)
	if err != nil {
		return false
	}

	defer file.Close()
	return true
}

// CopyFile
//
//	@Description: 复制文件
//	@param srcPath
//	@param dstPath
//	@return error
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

// CopyDir
//
//	@Description: 复制目录到目标路径
//	@param srcPath
//	@param dstPath
//	@return error
func CopyDir(srcPath string, dstPath string) error {
	srcInfo, err := os.Stat(srcPath)
	if err != nil {
		return fmt.Errorf("failed to get source directory info: %w", err)
	}

	if !srcInfo.IsDir() {
		return fmt.Errorf("source path is not a directory: %s", srcPath)
	}

	err = os.MkdirAll(dstPath, 0755)
	if err != nil {
		return fmt.Errorf("failed to create destination directory: %w", err)
	}

	entries, err := os.ReadDir(srcPath)
	if err != nil {
		return fmt.Errorf("failed to read source directory: %w", err)
	}

	for _, entry := range entries {
		srcDir := filepath.Join(srcPath, entry.Name())
		dstDir := filepath.Join(dstPath, entry.Name())

		if entry.IsDir() {
			err := CopyDir(srcDir, dstDir)
			if err != nil {
				return err
			}
		} else {
			err := CopyFile(srcDir, dstDir)
			if err != nil {
				return err
			}
		}
	}

	return nil
}

// CreateDir
//
//	@Description: 创建目录
//	@param absPath
//	@return error
func CreateDir(absPath string) error {
	// return os.MkdirAll(path.Dir(absPath), os.ModePerm)
	return os.MkdirAll(absPath, os.ModePerm)
}

// RemoveFile
//
//	@Description: 删除文件
//	@param path
//	@return error
func RemoveFile(path string) error {
	return os.Remove(path)
}

// ReadFileToString
//
//	@Description: 读取文件到字符串
//	@param path
//	@return string
//	@return error
func ReadFileToString(path string) (string, error) {
	bytes, err := os.ReadFile(path)
	if err != nil {
		return "", err
	}
	return string(bytes), nil
}

// ReadFileByLine
//
//	@Description:按行读取文件内容
//	@param path
//	@return []string
//	@return error
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

// FileMode
//
//	@Description:获取文件信息
//	@param path
//	@return fs.FileMode
//	@return error
func FileMode(path string) (fs.FileMode, error) {
	fi, err := os.Lstat(path)
	if err != nil {
		return 0, err
	}
	return fi.Mode(), nil
}

// MiMeType
//
//	@Description: 获取文件mime类型,字符串或*os.File
//	@param file f, _ := os.Open("./file.go") 或"1.txt"
//	@return string
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

// CurrentPath
//
//	@Description: 当前位置绝对路径
//	@return string
func CurrentPath() string {
	var absPath string
	_, filename, _, ok := runtime.Caller(1)
	if ok {
		absPath = filepath.Dir(filename)
	}

	return absPath
}

// FileSize
//
//	@Description: 文件大小字节
//	@param path
//	@return int64
//	@return error
func FileSize(path string) (int64, error) {
	f, err := os.Stat(path)
	if err != nil {
		return 0, err
	}
	return f.Size(), nil
}

// DirSize
//
//	@Description: 目录大小字节
//	@param path
//	@return int64
//	@return error
func DirSize(path string) (int64, error) {
	var size int64
	err := filepath.WalkDir(path, func(_ string, d os.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if !d.IsDir() {
			info, err := d.Info()
			if err != nil {
				return err
			}
			size += info.Size()
		}
		return err
	})
	return size, err
}

// DownloadFile
//
//	@Description: 下载文件
//	@param filepath
//	@param url
//	@return error
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

// OpenURL
//
//	@Description: 访问URL,用于cli
//	@param url
func OpenURL(url string) {
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

// MTime
//
//	@Description: 文件修改时间戳
//	@param filepath
//	@return int64
//	@return error
func MTime(filepath string) (int64, error) {
	f, err := os.Stat(filepath)
	if err != nil {
		return 0, err
	}
	return f.ModTime().Unix(), nil
}

// Sha
//
//	@Description: 返回文件sha值，参数`shaType` 应传值为: 1, 256，512
//	@param filepath
//	@param shaType
//	@return string
//	@return error
func Sha(filepath string, shaType ...int) (string, error) {
	file, err := os.Open(filepath)
	if err != nil {
		return "", err
	}
	defer file.Close()

	h := sha1.New()
	if len(shaType) > 0 {
		if shaType[0] == 1 {
			h = sha1.New()
		} else if shaType[0] == 256 {
			h = sha256.New()
		} else if shaType[0] == 512 {
			h = sha512.New()
		} else {
			return "", errors.New("param `shaType` should be 1, 256 or 512")
		}
	}

	_, err = io.Copy(h, file)

	if err != nil {
		return "", err
	}

	sha := fmt.Sprintf("%x", h.Sum(nil))

	return sha, nil

}

// ReadCsvFile
//
//	@Description: 读取csv文件
//	@param filepath
//	@param delimiter
//	@return [][]string
//	@return error
func ReadCsvFile(filepath string, delimiter ...rune) ([][]string, error) {
	f, err := os.Open(filepath)
	if err != nil {
		return nil, err
	}
	defer f.Close()

	reader := csv.NewReader(f)
	if len(delimiter) > 0 {
		reader.Comma = delimiter[0]
	}

	records, err := reader.ReadAll()
	if err != nil {
		return nil, err
	}

	return records, nil
}

// WriteCsvFile
//
//	data := [][]string{
//	       {"Lili", "22", "female"},
//	       {"Jim", "21", "male"},
//	   }
//		@Description: 写入csv文件
//		@param filepath
//		@param records
//		@param append 是否追加
//		@param delimiter
//		@return error
func WriteCsvFile(filepath string, records [][]string, append bool, delimiter ...rune) error {
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
	// 设置默认分隔符为逗号，除非另外指定
	if len(delimiter) > 0 {
		writer.Comma = delimiter[0]
	} else {
		writer.Comma = ','
	}

	// 遍历所有记录并处理包含分隔符或双引号的单元格
	for i := range records {
		for j := range records[i] {
			records[i][j] = escapeCSVField(records[i][j], writer.Comma)
		}
	}

	return writer.WriteAll(records)
}
func escapeCSVField(field string, delimiter rune) string {
	// 替换所有的双引号为两个双引号
	escapedField := strings.ReplaceAll(field, "\"", "\"\"")

	// 如果字段包含分隔符、双引号或换行符，用双引号包裹整个字段
	if strings.ContainsAny(escapedField, string(delimiter)+"\"\n") {
		escapedField = fmt.Sprintf("\"%s\"", escapedField)
	}

	return escapedField
}

// WriteMapsToCsv
//
//		@Description: 将map切片写入csv文件中
//		@param filepath
//		@param records []map[string]any{
//	       {"Name": "Lili", "Age": "22", "Gender": "female"},
//	       {"Name": "Jim", "Age": "21", "Gender": "male"},
//	   }
//		@param appendToExistingFile 是否追加
//		@param delimiter 分隔符号 ;
//		@param headers []string{"Name", "Age", "Gender"}
//		@return error
func WriteMapsToCsv(filepath string, records []map[string]any, appendToExistingFile bool, delimiter rune,
	headers ...[]string) error {
	for _, record := range records {
		for _, value := range record {
			if !isCsvSupportedType(value) {
				return errors.New("unsupported value type detected; only basic types are supported: \nbool, rune, string, int, int64, float32, float64, uint, byte, complex128, complex64, uintptr")
			}
		}
	}

	var columnHeaders []string
	if len(headers) > 0 {
		columnHeaders = headers[0]
	} else {
		for key := range records[0] {
			columnHeaders = append(columnHeaders, key)
		}
		// sort keys in alphabeta order
		sort.Strings(columnHeaders)
	}

	var datasToWrite [][]string
	if !appendToExistingFile {
		datasToWrite = append(datasToWrite, columnHeaders)
	}

	for _, record := range records {
		var row []string
		for _, h := range columnHeaders {
			row = append(row, fmt.Sprintf("%v", record[h]))
		}
		datasToWrite = append(datasToWrite, row)
	}

	return WriteCsvFile(filepath, datasToWrite, appendToExistingFile, delimiter)
}
func isCsvSupportedType(v interface{}) bool {
	switch v.(type) {
	case bool, rune, string, int, int64, float32, float64, uint, byte, complex128, complex64, uintptr:
		return true
	default:
		return false
	}
}

// WriteStringToFile
//
//	@Description: 写字符串到文件
//	@param filepath
//	@param content
//	@param append
//	@return error
func WriteStringToFile(filepath string, content string, append bool) error {
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

// WriteBytesToFile
//
//	@Description: bytes写入文件
//	@param filepath
//	@param content
//	@return error
func WriteBytesToFile(filepath string, content []byte) error {
	f, err := os.OpenFile(filepath, os.O_WRONLY|os.O_CREATE|os.O_TRUNC, 0644)
	if err != nil {
		return err
	}

	defer f.Close()

	_, err = f.Write(content)
	return err
}

// ReadFile
// reader, fn, err := fileutil.ReadFile("https://httpbin.org/robots.txt")
//
//	   if err != nil {
//	       return
//	   }
//	   defer fn()
//
//	   dat, err := io.ReadAll(reader)
//	   if err != nil {
//	       return
//	   }
//
//	   fmt.Println(string(dat))
//		@Description: 读取文件或URL文件
//		@param path
//		@return reader
//		@return closeFn
//		@return err
func ReadFile(path string) (reader io.ReadCloser, closeFn func(), err error) {
	switch {
	case IsUrl(path):
		resp, err := http.Get(path)
		if err != nil {
			return nil, func() {}, err
		}
		return resp.Body, func() { resp.Body.Close() }, nil
	case IsExist(path):
		reader, err := os.Open(path)
		if err != nil {
			return nil, func() {}, err
		}
		return reader, func() { reader.Close() }, nil
	default:
		return nil, func() {}, errors.New("unknown file type")
	}
}

// Drop[T any, Slice ~[]T]
//
//	@Description: slice开头删除元素
//	@param collection
//	@param n
//	@return Slice
func Drop[T any, Slice ~[]T](collection Slice, n int) Slice {
	if len(collection) <= n {
		return make(Slice, 0)
	}

	result := make(Slice, 0, len(collection)-n)

	return append(result, collection[n:]...)
}

// DropRight[T any, Slice ~[]T]
//
//	@Description: slice末尾删除元素
//	@param collection
//	@param n
//	@return Slice
func DropRight[T any, Slice ~[]T](collection Slice, n int) Slice {
	if len(collection) <= n {
		return Slice{}
	}

	result := make(Slice, 0, len(collection)-n)
	return append(result, collection[:len(collection)-n]...)
}

// DropByIndex[T any]
//
//	@Description: 根据索引删除元素
//	@param collection
//	@param indexes
//	@return []T
func DropByIndex[T any](collection []T, indexes ...int) []T {
	initialSize := len(collection)
	if initialSize == 0 {
		return make([]T, 0)
	}

	for i := range indexes {
		if indexes[i] < 0 {
			indexes[i] = initialSize + indexes[i]
		}
	}

	indexes = Uniq(indexes)
	sort.Ints(indexes)

	result := make([]T, 0, initialSize)
	result = append(result, collection...)

	for i := range indexes {
		if indexes[i]-i < 0 || indexes[i]-i >= initialSize-i {
			continue
		}

		result = append(result[:indexes[i]-i], result[indexes[i]-i+1:]...)
	}

	return result
}

// Entries[K comparable, V any]
//
//	@Description: map键值对转换数组
//	@param in
//	@return []Entry[K
//	@return V]
func Entries[K comparable, V any](in map[K]V) []Entry[K, V] {
	entries := make([]Entry[K, V], 0, len(in))

	for k := range in {
		entries = append(entries, Entry[K, V]{
			Key:   k,
			Value: in[k],
		})
	}

	return entries
}
func Empty[T any]() T {
	var zero T
	return zero
}

// Ellipsis
//
//	@Description: 字符串截取
//	@param str
//	@param length
//	@return string
func Ellipsis(str string, length uint) string {
	str = strings.TrimSpace(str)
	size := uint(RuneLength(str))
	if size > length {
		if size < 3 || length < 3 {
			return "..."
		}
		return Substring(str, 0, length) + "..."
	}

	return str
}

// EmojiDecode
//
//	@Description: emoji解码
//	@param s
//	@return string
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

// EmojiEncode
//
//	@Description: emoji编码
//	@param s
//	@return string
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

// Emoji
//
//	@Description: emoji转换实体直接显示
//	@param s
//	@return ss
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

// FromEntries[K comparable, V any]
//
//	@Description: 键值对数组转换map
//	@param entries
//	@param V]
//	@return map[K]V
func FromEntries[K comparable, V any](entries []Entry[K, V]) map[K]V {
	out := make(map[K]V, len(entries))

	for i := range entries {
		out[entries[i].Key] = entries[i].Value
	}

	return out
}

// FirstOr[T any]
//
//	@Description: 返回集合第一个元素,不存在则是默认值
//	@param collection
//	@param fallback
//	@return T
func First[T any](collection []T, fallback T) T {
	i, err := Nth(collection, 0)
	if err != nil {
		return fallback
	}
	return i

}

// FindKey[K comparable, V comparable]
//
//	@Description: 在map中查找值的键
//	@param object
//	@param value
//	@return K
//	@return bool
func FindKey[K comparable, V comparable](object map[K]V, value V) (K, bool) {
	for k := range object {
		if object[k] == value {
			return k, true
		}
	}

	return Empty[K](), false
}

// ForEach[T any]
//
//	@Description:循环输出
//	@param collection
//	@param iteratee
func ForEach[T any](collection []T, iteratee func(item T, index int)) {
	for i := range collection {
		iteratee(collection[i], i)
	}
}

// Flatten[T any, Slice ~[]T]
//
//	@Description: 多维数组转换一维
//	@param collection
//	@return Slice
func Flatten[T any, Slice ~[]T](collection []Slice) Slice {
	totalLen := 0
	for i := range collection {
		totalLen += len(collection[i])
	}

	result := make(Slice, 0, totalLen)
	for i := range collection {
		result = append(result, collection[i]...)
	}

	return result
}

// HasKey[K comparable, V any]
//
//	@Description:判断key是否存在
//	@param in
//	@param key
//	@return bool
func HasKey[K comparable, V any](in map[K]V, key K) bool {
	_, ok := in[key]
	return ok
}

// Concat[T any, Slice ~[]T]
//
//	@Description: 合并数组并排序
//	@param collections
//	@return Slice
func Concat[T any, Slice ~[]T](collections ...Slice) Slice {
	if len(collections) == 0 {
		return Slice{}
	}

	maxSize := 0
	totalSize := 0
	for i := range collections {
		size := len(collections[i])
		totalSize += size
		if size > maxSize {
			maxSize = size
		}
	}

	if maxSize == 0 {
		return Slice{}
	}

	result := make(Slice, totalSize)

	resultIdx := 0
	for i := 0; i < maxSize; i++ {
		for j := range collections {
			if len(collections[j])-1 < i {
				continue
			}

			result[resultIdx] = collections[j][i]
			resultIdx++
		}
	}

	return result
}

// ImgToEnbase64
//
//	@Description: 图片文件转换成base64字符
//	@param filename
//	@return s
func ImgToEnbase64(filename string) (s string) {
	ext := filepath.Ext(filename)
	ext = strings.TrimLeft(ext, ".")
	srcByte, _ := os.ReadFile(filename)
	s = Base64Encode(string(srcByte))
	s = "data:image/" + ext + ";base64," + s
	return
}

// ImgToDebase64
//
//	@Description: 图片解码base64成文件
//	@param path
//	@param data
//	@return ps
func ImgToDebase64(path, data string) (ps string) {
	re := regexp.MustCompile(`^(data:\s*image\/(\w+);base64,)`)
	r := re.FindStringSubmatch(data)
	ext := r[2]
	bs := strings.Replace(data, r[1], "", -1)
	CreateDir(path)
	ps = path + "/" + Sha1(data) + "." + ext
	bs = Base64Decode(bs)
	os.WriteFile(ps, []byte(bs), 0666)
	return ps
}

// Intersect[T comparable, Slice ~[]T]
//
//	@Description: 计算交集
//	@param list1
//	@param list2
//	@return Slice
func Intersect[T comparable, Slice ~[]T](list1 Slice, list2 Slice) Slice {
	result := Slice{}
	seen := map[T]struct{}{}

	for i := range list1 {
		seen[list1[i]] = struct{}{}
	}

	for i := range list2 {
		if _, ok := seen[list2[i]]; ok {
			result = append(result, list2[i])
		}
	}

	return result
}

// Invert[K comparable, V comparable]
//
//	@Description: map键值对调
//	@param in
//	@return map[V]K
func Invert[K comparable, V comparable](in map[K]V) map[V]K {
	out := make(map[V]K, len(in))

	for k := range in {
		out[in[k]] = k
	}

	return out
}

// IsNil
//
//	@Description: 判断是否nil
//	@param x
//	@return bool
func IsNil(x any) bool {
	defer func() { recover() }() // nolint:errcheck
	return x == nil || reflect.ValueOf(x).IsNil()
}

// IsWindows
//
//	@Description: 是否win系统
//	@return bool
func IsWindows() bool {
	return runtime.GOOS == "windows"
}

// IsLinux
//
//	@Description: 是否linux
//	@return bool
func IsLinux() bool {
	return runtime.GOOS == "linux"
}

// IsMac
//
//	@Description: 是否Mac
//	@return bool
func IsMac() bool {
	return runtime.GOOS == "darwin"
}

// IsExist
//
//	@Description: 判断文件或目录是否存在
//	@param path
//	@return bool
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

// IsDir
//
//	@Description: 判断是否目录
//	@param path
//	@return bool
func IsDir(path string) bool {
	file, err := os.Stat(path)
	if err != nil {
		return false
	}
	return file.IsDir()
}

// IsZipFile
//
//	@Description: 是否zip压缩文件
//	@param filepath
//	@return bool
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

// IsLink
//
//	@Description: 判断文件是否链接
//	@param path
//	@return bool
func IsLink(path string) bool {
	fi, err := os.Lstat(path)
	if err != nil {
		return false
	}
	return fi.Mode()&os.ModeSymlink != 0
}

// IsEmail
//
//	@Description: 是否email
//	@param email
//	@return bool
func IsEmail(email string) bool {
	_, err := mail.ParseAddress(email)
	return err == nil

	// return emailMatcher.MatchString(email)
}

// IsChineseMobile check if the string is chinese mobile number.
//
//	@Description: 是否手机号
//	@param mobileNum
//	@return bool
func IsChineseMobile(mobileNum string) bool {
	return chineseMobileMatcher.MatchString(mobileNum)
}

// IsChineseIdNum
//
//	@Description: 是否身份证
//	@param id
//	@return bool
func IsChineseIdNum(id string) bool {
	// All characters should be numbers, and the last digit can be either x or X
	if !chineseIdMatcher.MatchString(id) {
		return false
	}

	// Verify province codes and complete all province codes according to GB/T2260
	_, ok := provinceKv[id[0:2]]
	if !ok {
		return false
	}

	// Verify birthday, must be greater than birthStartYear and less than the current year
	birthStr := fmt.Sprintf("%s-%s-%s", id[6:10], id[10:12], id[12:14])
	birthday, err := time.Parse("2006-01-02", birthStr)
	if err != nil || birthday.After(time.Now()) || birthday.Year() < birthStartYear {
		return false
	}

	// Verification code
	sum := 0
	for i, c := range id[:17] {
		v, _ := strconv.Atoi(string(c))
		sum += v * factor[i]
	}

	return verifyStr[sum%11] == strings.ToUpper(id[17:18])
}

// IsChinese
//
//	@Description: 是否包含中文
//	@param s
//	@return bool
func IsChinese(s string) bool {
	return chineseMatcher.MatchString(s)
}
func IsCreditCard(creditCart string) bool {
	return creditCardMatcher.MatchString(creditCart)
}

// IsASCII
//
//	@Description: 是否ascii
//	@param str
//	@return bool
func IsASCII(str string) bool {
	for i := 0; i < len(str); i++ {
		if str[i] > unicode.MaxASCII {
			return false
		}
	}
	return true
}

// IsBase64
//
//	@Description: 是否base64
//	@param base64
//	@return bool
func IsBase64(base64 string) bool {
	return base64Matcher.MatchString(base64)
}

// GetOsBits
//
//	@Description: 获取系统位数
//	@return int
func GetOsBits() int {
	return 32 << (^uint(0) >> 63)
}

// IsEmpty[T comparable]
//
//	@Description: 判断是否为空,0,""都是空
//	@param v
//	@return bool
func IsEmpty[T comparable](v T) bool {
	var zero T
	return zero == v
}

// IsNumber
//
//	@Description: 是否数字
//	@param v
//	@return bool
func IsNumber(v any) bool {
	return IsInt(v) || IsFloat(v)
}

// IsFloat
//
//	@Description: 是否浮点数
//	@param v
//	@return bool
func IsFloat(v any) bool {
	switch v.(type) {
	case float32, float64:
		return true
	}
	return false
}

// IsInt
//
//	@Description: 是否整数
//	@param v
//	@return bool
func IsInt(v any) bool {
	switch v.(type) {
	case int, int8, int16, int32, int64, uint, uint8, uint16, uint32, uint64, uintptr:
		return true
	}
	return false
}

// IsWeixin
//
//	@Description: 是否微信
//	@param r
//	@return bool
func IsWeixin(r *http.Request) bool {
	if strings.Index(r.UserAgent(), "icroMessenger") == -1 {
		return false
	} else {
		return true
	}
}

// IsString
//
//	@Description: 是否字符串
//	@param v
//	@return bool
func IsString(v any) bool {
	if v == nil {
		return false
	}
	switch v.(type) {
	case string:
		return true
	default:
		return false
	}
}

// IsGBK
//
//	@Description: 是否GBK
//	@param data
//	@return bool
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

// IsUtf8
//
//	@Description: 是否utf8
//	@param s
//	@return bool
func IsUtf8(s string) bool {
	return utf8.ValidString(s)
}

// IsJSON
//
//	@Description: 是否json
//	@param str
//	@return bool
func IsJSON(str string) bool {
	var js json.RawMessage
	return json.Unmarshal([]byte(str), &js) == nil
}

// IsIp
//
//	@Description: 是否IP
//	@param ipstr
//	@return bool
func IsIp(ipstr string) bool {
	ip := net.ParseIP(ipstr)
	return ip != nil
}

// IsIpV6
//
//	@Description: 是否ipv6
//	@param ipstr
//	@return bool
func IsIpV6(ipstr string) bool {
	ip := net.ParseIP(ipstr)
	if ip == nil {
		return false
	}
	return ip.To4() == nil && len(ip) == net.IPv6len
}

// IsUrl
//
//	@Description: 是否url
//	@param str
//	@return bool
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

	return urlMatcher.MatchString(str)
}

// IsStrongPassword
//
//	@Description: 是否强密码
//	@param password
//	@param length
//	@return bool
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

// IsWeakPassword
//
//	@Description: 是否弱密码数字或大小写
//	@param password
//	@return bool
func IsWeakPassword(password string) bool {
	var num, letter, special bool
	for _, r := range password {
		switch {
		case unicode.IsDigit(r):
			num = true
		case unicode.IsLetter(r):
			letter = true
		case unicode.IsSymbol(r), unicode.IsPunct(r):
			special = true
		}
	}

	return (num || letter) && !special
}

// IsHex
//
//	@Description: 是否16进制
//	@param v
//	@return bool
func IsHex(v string) bool {
	return hexMatcher.MatchString(v)
}

// IsBase64URL
//
//	@Description: 是否base64url
//	@param v
//	@return bool
func IsBase64URL(v string) bool {
	return base64URLMatcher.MatchString(v)
}

// IsJWT
//
//	@Description: 是否jwt
//	@param v
//	@return bool
func IsJWT(v string) bool {
	strings1 := strings.Split(v, ".")
	if len(strings1) != 3 {
		return false
	}

	for _, s := range strings1 {
		if !IsBase64URL(s) {
			return false
		}
	}

	return true
}

// IsLeapYear
//
//	@Description: 是否闰年
//	@param year
//	@return bool
func IsLeapYear(year int) bool {
	return year%4 == 0 && (year%100 != 0 || year%400 == 0)
}

// IndexOf[T comparable]
//
//	@Description: 元素在数组中首次出现的索引,没有-1
//	@param collection
//	@param element
//	@return int
func IndexOf[T comparable](collection []T, element T) int {
	for i := range collection {
		if collection[i] == element {
			return i
		}
	}

	return -1
}

// Join[T any]
//
//	@Description: 分隔符链接切片元素,切片转换字符串用分隔符链接
//	@param slice
//	@param separator
//	@return string
func Join[T any](slice []T, separator string) string {
	str := mapss(slice, func(_ int, item T) string {
		return fmt.Sprint(item)
	})

	return strings.Join(str, separator)
}
func mapss[T any, U any](slice []T, iteratee func(index int, item T) U) []U {
	result := make([]U, len(slice), cap(slice))

	for i := 0; i < len(slice); i++ {
		result[i] = iteratee(i, slice[i])
	}

	return result
}

// Keys[K comparable, V any]
//
//	@Description: 返回map的key组成的切片,去重用Uniq
//	@param in
//	@return []K
func Keys[K comparable, V any](in ...map[K]V) []K {
	size := 0
	for i := range in {
		size += len(in[i])
	}
	result := make([]K, 0, size)

	for i := range in {
		for k := range in[i] {
			result = append(result, k)
		}
	}

	return result
}

// LastIndexOf[T comparable]
//
//	@Description:数组中找到值的最后一次出现的索引，如果找不到该值，则返回 -1
//	@param collection
//	@param element
//	@return int
func LastIndexOf[T comparable](collection []T, element T) int {
	length := len(collection)

	for i := length - 1; i >= 0; i-- {
		if collection[i] == element {
			return i
		}
	}

	return -1
}
func Last[T any](collection []T, fallback T) T {
	i, err := Nth(collection, -1)
	if err != nil {
		return fallback
	}
	return i

}

// ListFileNames
//
//	@Description: 返回目录下所有文件名
//	@param path
//	@return []string
//	@return error
func ListFileNames(path string) ([]string, error) {
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

// MapToSlice[K comparable, V any, R any]
//
//	@Description: map转换slice
//	@param in
//	@param iteratee
//	@return []R
func MapToSlice[K comparable, V any, R any](in map[K]V, iteratee func(key K, value V) R) []R {
	result := make([]R, 0, len(in))

	for k := range in {
		result = append(result, iteratee(k, in[k]))
	}

	return result
}

// MapToQueryString
//
//	var m = map[string]any{
//	       "c": 3,
//	       "a": 1,
//	       "b": 2,
//	   }  a=1&b=2&c=3
//		@Description:map转换成http查询
//		@param param
//		@return string
func MapToQueryString(param map[string]any) string {
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

// Average [T Float | Integer]
//
//	@Description: 数组求平均值
//	@param collection
//	@return T
func Average[T Float | Integer](collection []T) T {
	var length = T(len(collection))
	if length == 0 {
		return 0
	}
	var sum = Sum(collection)
	return sum / length
}

// Min[T Ordered]
//
//	@Description: 切片求最小值
//	@param collection
//	@return T
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

// Max[T Ordered]
//
//	@Description: 切片求最大值
//	@param collection
//	@return T
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

// Md5
//
//	@Description: 计算字符串md5
//	@param s
//	@return string
func Md5(s string) string {
	h := md5.New()
	h.Write([]byte(s))
	return hex.EncodeToString(h.Sum(nil))
}

// Nth[T any, N Integer]
//
//	@Description: 返回索引处元素
//	@param collection
//	@param nth
//	@return T
//	@return error
func Nth[T any, N Integer](collection []T, nth N) (T, error) {
	n := int(nth)
	l := len(collection)
	if n >= l || -n > l {
		var t T
		return t, fmt.Errorf("nth: %d out of slice bounds", n)
	}

	if n >= 0 {
		return collection[n], nil
	}
	return collection[l+n], nil
}

// Comma[T Float | Integer | string]
//
//	@Description: 逗号分割数字或字符串,支持添加前缀
//	@param value
//	@param prefixSymbol
//	@return string
func Comma[T Float | Integer | string](value T, prefixSymbol string) string {
	numString := ToString(value)

	_, err := strconv.ParseFloat(numString, 64)
	if err != nil {
		return ""
	}

	isNegative := strings.HasPrefix(numString, "-")
	if isNegative {
		numString = numString[1:]
	}

	index := strings.Index(numString, ".")
	if index == -1 {
		index = len(numString)
	}

	for index > 3 {
		index -= 3
		numString = numString[:index] + "," + numString[index:]
	}

	if isNegative {
		numString = "-" + numString
	}

	return prefixSymbol + numString
}

// ColorHexToRGB
//
//	@Description: 十六进制转换rgb
//	@param colorHex
//	@return red
//	@return green
//	@return blue
func ColorHexToRGB(colorHex string) (red, green, blue int) {
	colorHex = strings.TrimPrefix(colorHex, "#")
	color64, err := strconv.ParseInt(colorHex, 16, 32)
	if err != nil {
		return
	}
	color := int(color64)
	return color >> 16, (color & 0x00FF00) >> 8, color & 0x0000FF
}

// ColorRGBToHex
//
//	@Description: rgb转换十六进制
//	@param red
//	@param green
//	@param blue
//	@return string
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

// PickByKeys[K comparable, V any, Map ~map[K]V]
//
//	@Description: 根据给定key选取map
//	@param in
//	@param keys
//	@return Map
func PickByKeys[K comparable, V any, Map ~map[K]V](in Map, keys []K) Map {
	r := Map{}
	for i := range keys {
		if v, ok := in[keys[i]]; ok {
			r[keys[i]] = v
		}
	}
	return r
}

// PickByValues[K comparable, V comparable, Map ~map[K]V]
//
//	@Description: 根据值选择map组成的新map
//	@param in
//	@param values
//	@return Map
func PickByValues[K comparable, V comparable, Map ~map[K]V](in Map, values []V) Map {
	r := Map{}
	for k := range in {
		if Contains(values, in[k]) {
			r[k] = in[k]
		}
	}
	return r
}

// Reverse[T any, Slice ~[]T]
//
//	@Description: 反序数组
//	@param collection
//	@return Slice
func Reverse[T any, Slice ~[]T](collection Slice) Slice {
	length := len(collection)
	half := length / 2

	for i := 0; i < half; i = i + 1 {
		j := length - 1 - i
		collection[i], collection[j] = collection[j], collection[i]
	}

	return collection
}

// RuneLength
//
//	@Description: 中文字符统计
//	@param str
//	@return int
func RuneLength(str string) int {
	return utf8.RuneCountInString(str)
}

// RandColor
//
//	@Description: 随机颜色
//	@return string
func RandColor() string {
	str := "abcdef0123456789"
	var s string
	for i := 0; i < 6; i++ {
		n := RandInt(0, 16)
		s += Substring(str, n, 1)
	}
	return "#" + s
}

// Replace[T comparable, Slice ~[]T]
//
//	@Description: 替换元素
//	@param collection
//	@param old
//	@param new
//	@param n -1是全部替换
//	@return Slice
func Replace[T comparable, Slice ~[]T](collection Slice, old T, new T, n int) Slice {
	result := make(Slice, len(collection))
	copy(result, collection)

	for i := range result {
		if result[i] == old && n != 0 {
			result[i] = new
			n--
		}
	}

	return result
}

// Range[T Integer | Float]
//
//	@Description: 生成数组
//	@param start
//	@param end
//	@param step 步长
//	@return []T
func Range[T Integer | Float](start, end, step T) []T {
	var result []T
	if start == end || step == 0 {
		return result
	}
	if start < end {
		if step < 0 {
			return result
		}
		for i := start; i < end; i += step {
			result = append(result, i)
		}
		return result
	}
	if step > 0 {
		return result
	}
	for i := start; i > end; i += step {
		result = append(result, i)
	}
	return result
}

// PointDistance
//
//	@Description: 计算两个坐标距离
//	@param x1
//	@param y1
//	@param x2
//	@param y2
//	@return float64
func PointDistance(x1, y1, x2, y2 float64) float64 {
	a := x1 - x2
	b := y1 - y2
	c := math.Pow(a, 2) + math.Pow(b, 2)

	return math.Sqrt(c)
}

// PasswordHash
//
//	@Description: 散列密码加密
//	@param password 密码
//	@return string 散列密码
//	@return error
func PasswordHash(password string) (string, error) {
	salt, _ := Salt(10)
	hash, err := Hash(password, salt)
	return hash, err
}

// PasswordVerify
//
//	@Description: 验证散列密码
//	@param password 密码
//	@param hash 散列密码
//	@return bool
func PasswordVerify(password, hash string) bool {
	is := Match(password, hash)
	return is
}

// RandomString
//
//	@Description:随机字符串,不包含oO
//	@param size
//	@param charset
//	@return string
func RandomString(size int) string {
	if size <= 0 {
		panic("lo.RandomString: Size parameter must be greater than 0")
	}
	charset := []rune("abcdefghijklmnpqrstuvwxyzABCDEFGHIJKLMNPQRSTUVWXYZ0123456789")
	sb := strings.Builder{}
	sb.Grow(size)
	letterIdBits := int(math.Log2(float64(nearestPowerOfTwo(len(charset)))))
	var letterIdMask int64 = 1<<letterIdBits - 1
	letterIdMax := 63 / letterIdBits
	for i, cache, remain := size-1, rand.Int64(), letterIdMax; i >= 0; {
		if remain == 0 {
			cache, remain = rand.Int64(), letterIdMax
		}
		if idx := int(cache & letterIdMask); idx < len(charset) {
			sb.WriteRune(charset[idx])
			i--
		}
		cache >>= letterIdBits
		remain--
	}
	return sb.String()
}
func nearestPowerOfTwo(cap int) int {
	maximumCapacity := math.MaxInt>>1 + 1
	n := cap - 1
	n |= n >> 1
	n |= n >> 2
	n |= n >> 4
	n |= n >> 8
	n |= n >> 16
	if n < 0 {
		return 1
	}
	if n >= maximumCapacity {
		return maximumCapacity
	}
	return n + 1
}

// Shuffle[T any, Slice ~[]T]
//
//	@Description: 洗牌打乱数组
//	@param collection
//	@return Slice
func Shuffle[T any, Slice ~[]T](collection Slice) Slice {
	rand.Shuffle(len(collection), func(i, j int) {
		collection[i], collection[j] = collection[j], collection[i]
	})

	return collection
}

// Subset[T any, Slice ~[]T]
//
//	@Description: slice截取
//	@param collection
//	@param offset 开始
//	@param length 长度
//	@return Slice
func Subset[T any, Slice ~[]T](collection Slice, offset int, length uint) Slice {
	size := len(collection)

	if offset < 0 {
		offset = size + offset
		if offset < 0 {
			offset = 0
		}
	}

	if offset > size {
		return Slice{}
	}

	if length > uint(size)-uint(offset) {
		length = uint(size - offset)
	}

	return collection[offset : offset+int(length)]
}

// Sha256
//
//	@Description: sha256字符串值
//	@param str
//	@return string
func Sha256(str string) string {
	sha256 := sha256.New()
	sha256.Write([]byte(str))
	return hex.EncodeToString(sha256.Sum([]byte("")))
}

// Sha512
//
//	@Description: sha512值
//	@param str
//	@return string
func Sha512(str string) string {
	sha512 := sha512.New()
	sha512.Write([]byte(str))
	return hex.EncodeToString(sha512.Sum([]byte("")))
}

// Substring[T ~string]
//
//	@Description: 子字符串截取
//	@param str
//	@param offset
//	@param length
//	@return T
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

// SplitEx
//
//	@Description: 字符串分割为切片
//	@param s
//	@param sep 分隔符号
//	@param removeEmptyString 是否移除空字符串
//	@return []string
func SplitEx(s, sep string, removeEmptyString bool) []string {
	if sep == "" {
		return []string{}
	}

	n := strings.Count(s, sep) + 1
	a := make([]string, n)
	n--
	i := 0
	sepSave := 0
	ignore := false

	for i < n {
		m := strings.Index(s, sep)
		if m < 0 {
			break
		}
		ignore = false
		if removeEmptyString {
			if s[:m+sepSave] == "" {
				ignore = true
			}
		}
		if !ignore {
			a[i] = s[:m+sepSave]
			s = s[m+len(sep):]
			i++
		} else {
			s = s[m+len(sep):]
		}
	}

	var ret []string
	if removeEmptyString {
		if s != "" {
			a[i] = s
			ret = a[:i+1]
		} else {
			ret = a[:i]
		}
	} else {
		a[i] = s
		ret = a[:i+1]
	}

	return ret
}

// Sum[T Float | Integer | Complex]
//
//	@Description: 数组求和
//	@param collection
//	@return T
func Sum[T Float | Integer | Complex](collection []T) T {
	var sum T = 0
	for i := range collection {
		sum += collection[i]
	}
	return sum
}

// Sort[T Ordered]
//
//	@Description: 切片排序,数组排序
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

// RoundToFloat[T Float | Integer]
//
//	@Description: 四舍五入返回 float64
//	@param x
//	@param n 保留小数位数
//	@return float64
func RoundToFloat[T Float | Integer](x T, n int) float64 {
	tmp := math.Pow(10.0, float64(n))
	x *= T(tmp)
	r := math.Round(float64(x))
	return r / tmp
}

// Percent
//
//	@Description: 计算百分比,保留n位小数
//	@param val
//	@param total
//	@param n
//	@return float64
func Percent(val, total float64, n int) float64 {
	if total == 0 {
		return float64(0)
	}
	tmp := val / total * 100
	result := RoundToFloat(tmp, n)

	return result
}

// RoundToString[T Float | Integer]
//
//	@Description: 四舍五入到字符串
//	@param x
//	@param n
//	@return string
func RoundToString[T Float | Integer](x T, n int) string {
	tmp := math.Pow(10.0, float64(n))
	x *= T(tmp)
	r := math.Round(float64(x))
	result := strconv.FormatFloat(r/tmp, 'f', n, 64)
	return result
}

// RandInt
//
//	@Description: 随机返回两个整数之间的数
//	@param min
//	@param max 不含最大值
//	@return int
func RandInt(min, max int) int {
	if min == max {
		return min
	}

	if max < min {
		min, max = max, min
	}

	if min == 0 && max == math.MaxInt {
		return rand.Int()
	}

	return rand.IntN(max-min) + min
}

// TruncRound[T Float | Integer]
//
//	@Description: 截断n位小数不四舍五入
//	@param x
//	@param n
//	@return T
func TruncRound[T Float | Integer](x T, n int) T {
	floatStr := fmt.Sprintf("%."+strconv.Itoa(n+1)+"f", x)
	temp := strings.Split(floatStr, ".")
	var newFloat string
	if len(temp) < 2 || n >= len(temp[1]) {
		newFloat = floatStr
	} else {
		newFloat = temp[0] + "." + temp[1][:n]
	}
	result, _ := strconv.ParseFloat(newFloat, 64)
	return T(result)
}

// TableToSlice
//
//	@Description: html表格转换切片,去除html标签
//	@param s
//	@return [][]string
func TableToSlice(s string) [][]string {
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

// FloorToFloat[T Float | Integer]
// FloorToFloat(3.14159, 2) 3.14
// FloorToFloat(5, 4) 5
//
//	@Description: 向下舍入/去尾法 保留n位
//	@param x
//	@param n
//	@return float64
func FloorToFloat[T Float | Integer](x T, n int) float64 {
	tmp := math.Pow(10.0, float64(n))
	x *= T(tmp)
	r := math.Floor(float64(x))
	return r / tmp
}

// CeilToFloat[T Float | Integer]
// CeilToFloat(3.14159, 1)3.2
// CeilToFloat(5, 4) 5
//
//	@Description: 向上舍入（进一法），保留n位小数
//	@param x
//	@param n
//	@return float64
func CeilToFloat[T Float | Integer](x T, n int) float64 {
	tmp := math.Pow(10.0, float64(n))
	x *= T(tmp)
	r := math.Ceil(float64(x))
	return r / tmp
}

// StripTags
//
//	@Description: 去除HTML中标签
//	@param content
//	@return string
func StripTags(content string) string {
	re := regexp.MustCompile(`<(.|\n)*?>`)
	return re.ReplaceAllString(content, "")
}

// Err
//
//	@Description: 显示错误
//	@param err
func Err(err error) {
	if err != nil {
		panic(err)
	}
}

// Sha1
//
//	@Description: 计算sha1值
//	@param str
//	@return string
func Sha1(str string) string {
	sha1 := sha1.New()
	sha1.Write([]byte(str))
	return hex.EncodeToString(sha1.Sum([]byte("")))
}

// Slice[T any, Slice ~[]T]
//
//	@Description: 截取切片,不包括结尾索引
//	@param collection
//	@param start
//	@param end
//	@return Slice
func Slice[T any, Slice ~[]T](collection Slice, start int, end int) Slice {
	size := len(collection)

	if start >= end {
		return Slice{}
	}

	if start > size {
		start = size
	}
	if start < 0 {
		start = 0
	}

	if end > size {
		end = size
	}
	if end < 0 {
		end = 0
	}

	return collection[start:end]
}

// Splice[T any, Slice ~[]T]
//
//	@Description: 在索引处插入多个值
//	@param collection
//	@param i
//	@param elements
//	@return Slice
func Splice[T any, Slice ~[]T](collection Slice, i int, elements ...T) Slice {
	sizeCollection := len(collection)
	sizeElements := len(elements)
	output := make(Slice, 0, sizeCollection+sizeElements) // preallocate memory for the output slice

	if sizeElements == 0 {
		return append(output, collection...) // simple copy
	} else if i > sizeCollection {
		// positive overflow
		return append(append(output, collection...), elements...)
	} else if i < -sizeCollection {
		// negative overflow
		return append(append(output, elements...), collection...)
	} else if i < 0 {
		// backward
		i = sizeCollection + i
	}

	return append(append(append(output, collection[:i]...), elements...), collection[i:]...)
}

// SliceToMap[T any, K comparable, V any]
//
//	@Description: slice转换map
//	@param collection
//	@param transform
//	@return map[K]V
func SliceToMap[T any, K comparable, V any](collection []T, transform func(item T) (K, V)) map[K]V {
	result := make(map[K]V, len(collection))

	for i := range collection {
		k, v := transform(collection[i])
		result[k] = v
	}

	return result
}

// RandomSlice[T any, Slice ~[]T]
//
//	@Description:数组中随机返回n个元素
//	@param collection
//	@param count
//	@return Slice
func RandomSlice[T any, Slice ~[]T](collection Slice, count int) Slice {
	size := len(collection)

	copy := append(Slice{}, collection...)

	results := Slice{}

	for i := 0; i < size && i < count; i++ {
		copyLength := size - i

		index := rand.IntN(size - i)
		results = append(results, copy[index])

		// Removes element.
		// It is faster to swap with last element and remove it.
		copy[index] = copy[copyLength-1]
		copy = copy[:copyLength-1]
	}

	return results
}

// Times[T any]
//
//	@Description: 调用多次迭代
//	@param count
//	@param iteratee
//	@return []T
func Times[T any](count int, iteratee func(index int) T) []T {
	result := make([]T, count)

	for i := 0; i < count; i++ {
		result[i] = iteratee(i)
	}

	return result
}

// Timestamp
//
//	@Description: 当前秒级时间戳
//	@param timezone
//	@return int64
func Timestamp(timezone ...string) int64 {
	t := time.Now()

	if timezone != nil && timezone[0] != "" {
		loc, err := time.LoadLocation(timezone[0])
		if err != nil {
			return 0
		}

		t = t.In(loc)
	}

	return t.Unix()
}

// TimestampToTime
//
//	@Description: 时间戳转换go时间
//	@param t
//	@return time.Time
func TimestampToTime(t int64) time.Time {
	const timeLayout = "2006-01-02 15:04:05"
	str := time.Unix(t, 0).Format(timeLayout)
	t1, _ := TimestrToTime(str, "yyyy-mm-dd hh:mm:ss")
	return t1
}

// TimestampToStr
//
//	@Description: 时间戳转换时间字符串
//	@param t
//	@return string
func TimestampToStr(t int64) string {
	return TimeToStr(TimestampToTime(t), "yyyy-mm-dd hh:mm:ss")
}

// TimeAddMinute
//
//	@Description: 添加减少分钟
//	@param t
//	@param minute
//	@return time.Time
func TimeAddMinute(t time.Time, minute int64) time.Time {
	return t.Add(time.Minute * time.Duration(minute))
}

// TimeAddHour add or sub hour to the time.
//
//	@Description: 添加减少小时
//	@param t
//	@param hour
//	@return time.Time
func TimeAddHour(t time.Time, hour int64) time.Time {
	return t.Add(time.Hour * time.Duration(hour))
}

// TimeAddDay
//
//	@Description: 加减日期,实现昨天明天
//	@param t
//	@param day
//	@return time.Time
func TimeAddDay(t time.Time, day int64) time.Time {
	return t.Add(24 * time.Hour * time.Duration(day))
}

// TimeAddYear
//
//	@Description: 添加减少年
//	@param t
//	@param year
//	@return time.Time
func TimeAddYear(t time.Time, year int64) time.Time {
	return t.Add(365 * 24 * time.Hour * time.Duration(year))
}

// TimeDaysBetween
//
//	@Description: 日期之间天数差
//	@param start
//	@param end
//	@return int
func TimeDaysBetween(start, end time.Time) int {
	duration := end.Sub(start)
	days := int(duration.Hours() / 24)

	return days
}

// GetDate
//
//	@Description: 日期
//	@return string
func GetDate() string {
	return time.Now().Format("2006-01-02")
}

// GetTime
//
//	@Description: 时间
//	@return string
func GetTime() string {
	return time.Now().Format("15:04:05")
}

// GetDateTime
//
//	@Description: 日期时间
//	@return string
func GetDateTime() string {
	return time.Now().Format("2006-01-02 15:04:05")
}

// GetAppPath
//
//	@Description: 获取当前程序路径
//	@return string
func GetAppPath() string {
	file, _ := exec.LookPath(os.Args[0])
	path, _ := filepath.Abs(file)
	index := strings.LastIndex(path, string(os.PathSeparator))
	return path[:index]
}

// GetIps
//
//	@Description: 获取本地ip列表
//	@return []string
func GetIps() []string {
	var ips []string

	addrs, err := net.InterfaceAddrs()
	if err != nil {
		return ips
	}

	for _, addr := range addrs {
		ipNet, isValid := addr.(*net.IPNet)
		if isValid && !ipNet.IP.IsLoopback() {
			if ipNet.IP.To4() != nil {
				ips = append(ips, ipNet.IP.String())
			}
		}
	}
	return ips
}
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

// HideString
//
//	@Description:隐藏字符串中某些字符
//	@param origin
//	@param start 开始
//	@param end 结束
//	@param replaceChar 要替换如 *
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

// IsPublicIP
//
//	@Description: 是否公网IP
//	@param IP
//	@return bool
func IsPublicIP(IP net.IP) bool {
	if IP.IsLoopback() || IP.IsLinkLocalMulticast() || IP.IsLinkLocalUnicast() {
		return false
	}
	if ip4 := IP.To4(); ip4 != nil {
		switch {
		case ip4[0] == 10:
			return false
		case ip4[0] == 172 && ip4[1] >= 16 && ip4[1] <= 31:
			return false
		case ip4[0] == 192 && ip4[1] == 168:
			return false
		default:
			return true
		}
	}
	return false
}

// IsInternalIP
//
//	@Description: 是否内网IP
//	@param IP
//	@return bool
func IsInternalIP(IP net.IP) bool {
	if IP.IsLoopback() {
		return true
	}
	if ip4 := IP.To4(); ip4 != nil {
		return ip4[0] == 10 ||
			(ip4[0] == 172 && ip4[1] >= 16 && ip4[1] <= 31) ||
			(ip4[0] == 169 && ip4[1] == 254) ||
			(ip4[0] == 192 && ip4[1] == 168)
	}
	return false
}

// GetInternalIp
//
//	@Description: 获取内部ipv4
//	@return string
func GetInternalIp() string {
	addrs, err := net.InterfaceAddrs()
	if err != nil {
		panic(err.Error())
	}

	for _, addr := range addrs {
		var ip net.IP
		switch v := addr.(type) {
		case *net.IPNet:
			ip = v.IP
		case *net.IPAddr:
			ip = v.IP
		}

		if ip != nil && (ip.IsLinkLocalUnicast() || ip.IsGlobalUnicast()) {
			continue
		}

		if ipv4 := ip.To4(); ipv4 != nil {
			return ipv4.String()
		}
	}

	return ""
}

// GetMacAddrs
//
//	@Description: 获取Mac地址
//	@return []string
func GetMacAddrs() []string {
	var macAddrs []string

	nets, err := net.Interfaces()
	if err != nil {
		return macAddrs
	}

	for _, net := range nets {
		macAddr := net.HardwareAddr.String()
		if len(macAddr) == 0 {
			continue
		}
		macAddrs = append(macAddrs, macAddr)
	}

	return macAddrs
}

// EncodeUrl
// ?a=1&b=[2] -> ?a=1&b=%5B2%5D
//
//	@Description: 编码url
//	@param urlStr
//	@return string
//	@return error
func EncodeUrl(urlStr string) (string, error) {
	URL, err := url.Parse(urlStr)
	if err != nil {
		return "", err
	}

	URL.RawQuery = URL.Query().Encode()

	return URL.String(), nil
}

// TimeToStr
//
//	@Description: 时间转换字符串格式化
//	@param t
//	@param format
//	@param timezone
//	@return string
func TimeToStr(t time.Time, format string, timezone ...string) string {
	tf, ok := timeFormat[strings.ToLower(format)]
	if !ok {
		return ""
	}

	if timezone != nil && timezone[0] != "" {
		loc, err := time.LoadLocation(timezone[0])
		if err != nil {
			return ""
		}
		return t.In(loc).Format(tf)
	}
	return t.Format(tf)
}

// TimestrToTime
//
//	@Description: 字符串转换go时间格式
//	@param str
//	@param format
//	@param timezone
//	@return time.Time
//	@return error
func TimestrToTime(str, format string, timezone ...string) (time.Time, error) {
	tf, ok := timeFormat[strings.ToLower(format)]
	if !ok {
		return time.Time{}, fmt.Errorf("format %s not support", format)
	}

	if timezone != nil && timezone[0] != "" {
		loc, err := time.LoadLocation(timezone[0])
		if err != nil {
			return time.Time{}, err
		}

		return time.ParseInLocation(tf, str, loc)
	}

	return time.Parse(tf, str)
}

// TimestrToTimestamp
//
//	@Description: 时间字符串转换时间戳
//	@param s
//	@return int64
func TimestrToTimestamp(s string) int64 {
	const timeLayout = "2006-01-02 15:04:05"
	loc := time.FixedZone("CST", 8*3600)
	tt, _ := time.ParseInLocation(timeLayout, s, loc)
	return tt.Unix()
}

// TimeLine
//
//	@Description: 时间戳友好显示
//	@param t
//	@return string
func TimeLine(t int64) string {
	now := time.Now().Unix()
	var xx string
	if now <= t {
		xx = TimeToStr(TimestampToTime(t), "yyyy-mm-dd hh:mm:ss")
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

// ToAnySlice[T any]
//
//	@Description: 转换成any类型切片
//	@param collection
//	@return []any
func ToAnySlice[T any](collection []T) []any {
	result := make([]any, len(collection))
	for i := range collection {
		result[i] = collection[i]
	}
	return result
}

// ToString
//
//	@Description: 任意类型转换字符串
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
	}
}

// ToUrlBase64
//
//	@Description: 转换成urlbase64
//	@param value
//	@return string
func ToUrlBase64(value any) string {
	if value == nil || (reflect.ValueOf(value).Kind() == reflect.Ptr && reflect.ValueOf(value).IsNil()) {
		return ""
	}
	switch value.(type) {
	case []byte:
		return base64.URLEncoding.EncodeToString(value.([]byte))
	case string:
		return base64.URLEncoding.EncodeToString([]byte(value.(string)))
	case error:
		return base64.URLEncoding.EncodeToString([]byte(value.(error).Error()))
	default:
		marshal, err := json.Marshal(value)
		if err != nil {
			return ""
		}
		return base64.URLEncoding.EncodeToString(marshal)
	}
}

// ToBool
//
//	@Description: 转换成布尔
//	@param s
//	@return bool
//	@return error
func ToBool(s string) (bool, error) {
	return strconv.ParseBool(s)
}

// ToSlice[T any]
//
//	@Description: 字符转换成切片
//	@param items
//	@return []T
func ToSlice[T any](items ...T) []T {
	result := make([]T, len(items))
	copy(result, items)

	return result
}

// ToBytes
//
//	@Description: 转换成字节切片
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

// ToChar
//
//	@Description: 转换字符切片
//	@param s
//	@return []string
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

// ToJson
//
//	@Description: 转换json
//	@param value
//	@return string
//	@return error
func ToJson(value any) (string, error) {
	result, err := json.Marshal(value)
	if err != nil {
		return "", err
	}

	return string(result), nil
}

// ToFloat
//
//	@Description: 转换float
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
//	@Description: 转换int
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

// Ternary[T any]
//
//	@Description:三元运算,相当于if-else,是语句
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
//	@Description: 三元运算,是函数
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

var (
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

// Trim
//
//	@Description: 去除字符串两边空格
//	@param str
//	@param characterMask 可指定其他去除字符
//	@return string
func Trim(str string, characterMask ...string) string {
	trimChars := DefaultTrimChars

	if len(characterMask) > 0 {
		trimChars += characterMask[0]
	}

	return strings.Trim(str, trimChars)
}

// Typeof
//
//	@Description: 返回变量类型
//	@param a
//	@return reflect.Type
func Typeof(a any) reflect.Type {
	return reflect.TypeOf(a)
}

// Uniq[T comparable, Slice ~[]T]
//
//	@Description:返回数组的无重复版本
//	@param collection
//	@return Slice
func Uniq[T comparable, Slice ~[]T](collection Slice) Slice {
	result := make(Slice, 0, len(collection))
	seen := make(map[T]struct{}, len(collection))

	for i := range collection {
		if _, ok := seen[collection[i]]; ok {
			continue
		}

		seen[collection[i]] = struct{}{}
		result = append(result, collection[i])
	}

	return result
}

// UniqBy[T any, U comparable, Slice ~[]T]
//
//	@Description: 返回无重复数组处理后结果
//	@param collection
//	@param iteratee
//	@return Slice
func UniqBy[T any, U comparable, Slice ~[]T](collection Slice, iteratee func(item T) U) Slice {
	result := make(Slice, 0, len(collection))
	seen := make(map[U]struct{}, len(collection))

	for i := range collection {
		key := iteratee(collection[i])

		if _, ok := seen[key]; ok {
			continue
		}

		seen[key] = struct{}{}
		result = append(result, collection[i])
	}

	return result
}

// Utf8ToGbk
//
//	@Description: uft8转gbk
//	@param bs
//	@return []byte
//	@return error
func Utf8ToGbk(bs []byte) []byte {
	b, _ :=GBK.NewEncoder().Bytes(bs)
	return b
}

// GbkToUtf8
//
//	@Description: gbk转换utf8
//	@param bs
//	@return []byte
//	@return error
func GbkToUtf8(bs []byte) []byte {
	b, _ := GBK.NewDecoder().Bytes(bs)
	return b

}

// Get
//
//	@Description: get请求http
//	@param u
//	@return string
func Get(u string) string {
	rs, _ := http.Get(u)
	defer rs.Body.Close()
	body, _ := io.ReadAll(rs.Body)
	if IsGBK(body) {
		return string(GbkToUtf8(body))
	}
	return string(body)
}

// Utf8ToUnicode
//
//	@Description: uft8转换unicode
//	@param str
//	@return string
func Utf8ToUnicode(str string) string {
	str1 := strconv.QuoteToASCII(str)
	return str1[1 : len(str1)-1]
}

// UnicodeToUtf8
// @Description: unicode转换utf8
// @param str
// @return string utf8
func UnicodeToUtf8(str string) string {
	str1, _ := strconv.Unquote(strings.Replace(strconv.Quote(str), `\\u`, `\u`, -1))
	return str1
}

// Union[T comparable, Slice ~[]T]
//
//	@Description: 并集
//	@param lists
//	@return Slice
func Union[T comparable, Slice ~[]T](lists ...Slice) Slice {
	var capLen int

	for _, list := range lists {
		capLen += len(list)
	}

	result := make(Slice, 0, capLen)
	seen := make(map[T]struct{}, capLen)

	for i := range lists {
		for j := range lists[i] {
			if _, ok := seen[lists[i][j]]; !ok {
				seen[lists[i][j]] = struct{}{}
				result = append(result, lists[i][j])
			}
		}
	}

	return result
}

// Uniqid
//
//	@Description: 生成时间戳随机字符串
//	@param prefix 前缀
//	@return string
func Uniqid(prefix string) string {
	now := time.Now()
	return fmt.Sprintf("%s%08x%05x", prefix, now.Unix(), now.UnixNano()%0x100000)
}

// Values[K comparable, V any]
//
//	@Description: 返回map的val组成的新切片
//	@param in
//	@return []V
func Values[K comparable, V any](in ...map[K]V) []V {
	size := 0
	for i := range in {
		size += len(in[i])
	}
	result := make([]V, 0, size)

	for i := range in {
		for k := range in[i] {
			result = append(result, in[i][k])
		}
	}

	return result
}

// ValueOr[K comparable, V any]
//
//	@Description: 根据key返回map值,不存在返回默认值
//	@param in
//	@param key
//	@param fallback 默认值
//	@return V
func ValueOr[K comparable, V any](in map[K]V, key K, fallback V) V {
	if v, ok := in[key]; ok {
		return v
	}
	return fallback
}

// Zip
//
//	@Description: 压缩文件或目录到zip
//	@param path
//	@param destPath
//	@return error
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

// UnZip
//
//	@Description: 解压zip
//	@param zipFile
//	@param destPath
//	@return error
func UnZip(zipFile string, destPath string) error {
	zipReader, err := zip.OpenReader(zipFile)
	if err != nil {
		return err
	}
	defer zipReader.Close()

	for _, f := range zipReader.File {
		// issue#62: fix ZipSlip bug
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

// ZipAppendEntry
//
//	@Description: 通过将单个文件或目录追加到现有的zip文件
//	@param fpath
//	@param destPath
//	@return error
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

// CliInput
//
//	@Description: cli输入
//	@param str
//	@param check nil
//	@return string
func CliInput(str string, check func(string) error) string {
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

var renderChooseQuestion = func(question string) string {
	return question + "\n"
}
var renderChooseOption = func(key, value string, size int) string {
	return fmt.Sprintf("%-"+fmt.Sprintf("%d", size+1)+"s %s\n", key+")", value)
}
var renderChooseQuery = func() string {
	return "Choose: "
}

// CliSelect
//
//	@Description: cli选择多项
//	@param question
//	@param choices
//	@return string
func CliSelect(question string, choices map[string]string) string {
	options := renderChooseQuestion(question)
	keys := []string{}
	max1 := 0
	for k, _ := range choices {
		if l := len(k); l > max1 {
			max1 = l
		}
		keys = append(keys, k)
	}
	sort.Strings(keys)
	for _, k := range keys {
		options += renderChooseOption(k, choices[k], max1)
	}
	options += renderChooseQuery()
	return CliInput(options, func(in string) error {
		if _, ok := choices[in]; ok {
			return nil
		} else {
			return fmt.Errorf("Choose one of: %s", strings.Join(keys, ", "))
		}
	})
}

var confirmRejection = "<warn>Please respond with \"y\" or \"n\"\n\n"
var confirmYesRegex = regexp.MustCompile(`^(?i)y(es)?$`)
var confirmNoRegex = regexp.MustCompile(`^(?i)no?$`)

// CliYesNo
//
//	@Description: cli选择yes/no
//	@param question
//	@return bool
func CliYesNo(question string) bool {
	cb := func(value string) error { return nil }
	for {
		res := CliInput(question, cb)
		if confirmYesRegex.MatchString(res) {
			return true
		} else if confirmNoRegex.MatchString(res) {
			return false
		} else {
			fmt.Printf(confirmRejection)
		}
	}
}
