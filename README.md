## github.com/logoove/go/cli

此包用于开发cli程序,修改自一个国外很少人用的包,用来开发简单cli还是不错的.
一个go/py/nodejs/flutter版本管理器 <https://github.com/logoove/xv>

```
// xv del 1.20.1 这种命令用 c.Args()[0]获取的就是第一个参数 1.20.1,长度使用c.NArg()==0来判断是否有参数
// xv install --ver=1.21.0  这种是设置名称获取 c.GetString("ver")

package main
import (
    "fmt"
    "github.com/logoove/go/cli"
    "strings"
    "os"
)
func main() {
app := cli.NewApp()
    app.Name = "cli"
    app.Version="1.0.0"
    app.Authors="Yoby\nWechat:logove"
    app.Description="程序描述"
    app.Usage="Golang版本管理工具"
    app.SeeAlso = "2021-"+strconv.Itoa(time.Now().Year())
    app.Commands = []*cli.Command{
        {
            Name:   "add",
            Usage:  "Add file contents to the index",
            Action: func(c *cli.Context) {
                fmt.Println("added files: ", strings.Join(c.Args(), ", "))
            },
        },
        {
            // alias name
            Name:   "a,all",
            Usage:  "Record changes to the repository",
            Flags:  []*cli.Flag {
                {
                    Name: "qq,q",
                    Usage: "commit message",
                },
            },
            Action: func(c *cli.Context) {
                fmt.Println(c.GetString("qq"))
            },
        },
    }
    app.Run(os.Args)
    }
```

## github.com/logoove/go/rest

用于开发简单的网站,这个包只有11kb非常小.

```
package main
import (
    "fmt"
    "github.com/logoove/go/rest"
)

func main() {
r := rest.New()
	r.Use(rest.CORS())
	r.LoadHTMLGlob("test/templates/*")
	r.Static("/static/", "test/static")
	r.GET("/json", func(c *rest.Context) {
		c.JSON(http.StatusOK, rest.H{"name": "中国"})
	})
	r.GET("/", func(c *rest.Context) {
		c.String(200, "Hi welcome 中国")
	})
	r.GET("/hello/:name", func(c *rest.Context) {
		c.String(200, c.Param("name")) //?name=qq 用c.Query("name")
	})
	v1 := r.Group("/v1")
	{
		v1.GET("/ht", func(c *rest.Context) {
			c.HTML(http.StatusOK, "css.tmpl", nil)
		})
	}
	v2 := r.Group("/v2")
	v2.GET("/s", rest.BasicAuth(func(c *rest.Context) {
		c.String(200, "Hi welcome 密码")
	}, "admin", "1234"))
	r.Run("0.0.0.0:8080")
}
```

## github.com/logoove/go/yo

一些常见的函数,参考了php,泛型,还有一些流行的库,放在了一起方便使用.原来的php名称废弃.
例如,返回时间戳: fmt.Print(yo.Time())
处理scile的foreach
nums := []int{1, 9, 3, 7, 5}
    var rx []int
    yo.ForEach(nums, func(k int, v int) {
        rx = append(rx, v+1)
    })
    fmt.Println(rx)
## github.com/logoove/go/sqlite
对goframe2.0+驱动包
## 备注

以上包都只含标准库,不含有任何第三方库.所以无需联网也能使用.
run.bat用来生成带图标和描述的win应用.