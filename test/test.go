package test

import (
	"bytes"
	_ "embed"
	"github.com/tc-hib/winres"
	"github.com/tc-hib/winres/version"
	"os"
	"strconv"
	"strings"
	"time"
)

//
// rsrc
//  @Description: 生成带图标exe和系统信息
//  @param qs 图标的字节码,格式是ico,用//go:embed icon.ico 申明
//  @param appName 应用名称
//  @param ver 版本号 1.0.0.0 四位数字用.隔开
//  @param lang 语言支持 cn中文 hk繁体 en英文
//  @param company 公司名
//  @param desc 应用简介
//  @param orig 应用原名 比如go.exe
//  @param lega 商标 比如 Yoby
// //go:embed icon.ico
// var p []byte
//rsrc(p,"xvgui for GUI", "1.0.0.1", "cn", "Yoby工作室", "一个开源GUI工具", "xvgui.exe", "Yoby")
//
func rsrc(qs []byte, appName string, ver string,lang string, company string, desc string, orig string, lega string) {
	//版本信息
	rs := winres.ResourceSet{}
	icon, _ := winres.LoadICO(bytes.NewReader(qs))
	rs.SetIcon(winres.Name("APPICON"), icon)
	str := strings.Split(ver, ".")
	var ver1 [4]uint16
	for i, val := range str {
		u64, _ := strconv.ParseUint(val, 10, 16)
		ver1[i]=uint16(u64)
	}
	vi := version.Info{
		FileVersion:   ver1,
		ProductVersion: ver1,
	}
	year := strconv.Itoa(time.Now().Year())
	langs:=map[string]uint16{"cn":0x804,"hk":0x404,"en":0x409}
	var lid uint16
	lid = langs[lang]//简体中文0x804 //繁中0x404 英文 0x409
	var copy strings.Builder
	copy.WriteString("Copyright©2020-")
	copy.WriteString(year)
	copy.WriteString(company)
	vi.Set(lid, version.ProductName, appName)   //产品名称
	vi.Set(lid, version.ProductVersion, ver)    //版本
	vi.Set(lid, version.CompanyName, company)   //公司
	vi.Set(lid, version.FileDescription, desc)  //产品描述
	vi.Set(lid, version.LegalCopyright, copy.String())   //版权
	vi.Set(lid, version.OriginalFilename, orig) //原名
	vi.Set(lid, version.LegalTrademarks, lega)  //商标
	rs.SetVersionInfo(vi)
	rs.SetManifest(winres.AppManifest{
		ExecutionLevel:      2,
		DPIAwareness:        3,
		UseCommonControlsV6: true,
	})
	out, _ := os.Create("rsrc_amd64.syso")
	defer out.Close()
	rs.WriteObject(out, winres.ArchAMD64)
}