// +build windows
package php

import (
	"fmt"
	"golang.org/x/sys/windows"
	"syscall"
)
func init(){
	WinColor=WinColors
	GetLangs=GetLangss
}
/**
 * @Description: 支持windows设置颜色
 * @param s 字符
 * @param i1 颜色
 */
func WinColors(s string, i1 string){
	c:=	map[string]int{
		"black":0,
		"blue":1,
		"green":2,
		"cyan":3,//青色
		"red":4,
		"purple":5,//紫色
		"yellow":6,//
		"white":15,
		"gray":8,
		"qing":3,
		"zi":5,
	}
	var i int
	if v, ok := c[i1]; ok {
		i=v
	}else{
		i=4
	}
		var kernel32	*syscall.LazyDLL
		kernel32=syscall.NewLazyDLL("kernel32.dll")
		proc := kernel32.NewProc("SetConsoleTextAttribute")
		handle, _, _ := proc.Call(uintptr(syscall.Stdout), uintptr(i))
		fmt.Print(s)
		handle, _, _ = proc.Call(uintptr(syscall.Stdout), uintptr(7))
		CloseHandle := kernel32.NewProc("CloseHandle")
		CloseHandle.Call(handle)
}
func GetLangss()string{
	s,_:=windows.GetUserPreferredUILanguages(8)
	return s[0]
}

