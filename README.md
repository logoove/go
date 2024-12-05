### golang工具包,包含路由,命令工具,函数库,sqlite
### 常用工具函数包

github.com/logoove/go/yo

一些常见的函数,参考了php,泛型,还有一些流行的库,放在了一起方便使用.原来的php名称废弃.
例如,返回时间戳: fmt.Print(yo.Timestamp())

处理scile的foreach
~~~
nums := []int{1, 9, 3, 7, 5}
    var rx []int
    yo.ForEach(nums, func(k int, v int) {
        rx = append(rx, v+1)
    })
    fmt.Println(rx)
~~~
### ico编码解码
github.com/logoove/go/ico
### test windows下生成带图标exe和系统信息
github.com/logoove/go/test 下面代码放入main.go的main函数中, 生成的exe文件运行, 就会创建rsrc_amd64.syso, 文件, 此时再次编译就会生成小文件带图标,只要syso存在就能自动编译到exe, 删除要重新生成.
编译小文件不带cmd `go build -ldflags "-s -w -H windowsgui"`
~~~
//go:embed icon.ico
var p []byte
rsrc(p,"xvgui for GUI", "1.0.0.1", "cn", "Yoby工作室", "一个开源GUI工具", "xvgui.exe", "Yoby")
~~~
### 命令行程序包
github.com/logoove/go/cli

此包用于开发cli程序,修改自一个国外很少人用的包,用来开发简单cli还是不错的.
我的作品xv用此包开发.

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
### 路由包类似gin

github.com/logoove/go/rest

用于开发简单的网站,这个包只有10KB,功能包含分组,简单鉴权,路由,模板,json,静态文件等.

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


### goframe2.0以上版本驱动包

_ "github.com/logoove/go/sqlite"
或者用goframe官方的
_ "github.com/gogf/gf/contrib/drivers/sqlite/v2"
~~~
package main

import (
	"fmt"
	"github.com/gogf/gf/v2/database/gdb"
	"github.com/gogf/gf/v2/frame/g"
	"github.com/gogf/gf/v2/net/ghttp"
	_ "github.com/logoove/go/sqlite"
)

func main() {
	s := g.Server()
	db, _ := gdb.New(gdb.ConfigNode{
		Link: "sqlite::@file(db.db)",
	})
	s.BindHandler("/", func(r *ghttp.Request) {
		isok, _ := db.Model("stat").Where("md5=? and types=?", "1", "1").One()
		r.Response.Write("hello 世界,值", isok["num"])
	})
	s.SetPort(8881)
	s.Run()
}
~~~


### 说明

以上包都只含标准库,不含有任何第三方库.所以无需联网也能使用.

