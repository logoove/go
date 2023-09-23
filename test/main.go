package main

import (
	"fmt"
	r "yo/rest"
	"yo/yo"
)

func main() {
	fmt.Print(yo.Time(), "\n")
	fmt.Printf(yo.Uniqid(""))
	//s := []string{"1", "2", "7"}
	//s1 := []int{1, 2, 3}
	arr := []int{7, 8, 9}
	arr1 := []int{7, 63, 99}
	fmt.Println(yo.Union(arr, arr1))
	fmt.Println(yo.Contain(arr, 11))
	mp := map[string]string{"a": "中国", "b": "日本"}
	fmt.Println(yo.HasKey(mp, "a"))
	vals := yo.Values(mp)
	fmt.Println(yo.Contain(vals, "日本"))
	fmt.Println(vals)
	fmt.Println(yo.GetAppPath())
	nums := []int{1, 9, 3, 7, 5}
	yo.Sort(nums)
	fmt.Println(nums)
	var rx []int
	yo.ForEach(nums, func(k int, v int) {
		rx = append(rx, v+1)
	})
	fmt.Println(rx)
	fmt.Println(len("中国abc"))
	fmt.Println(yo.RuneLength("中国abc"))
	var m = map[string]any{
		"c": 3,
		"a": 1,
		"b": 2,
	}
	fmt.Println(yo.Map2Http(m))
	fmt.Println(yo.GetIp())
	fmt.Println(yo.RandColor())
	fmt.Println(yo.InsertAt([]int{1, 2, 3, 4, 5, 6, 7}, 2, 10))
	fmt.Println(yo.HideTel("18299993344"))
	fmt.Println(yo.Invert(map[string]int{"foo": 1, "bar": 2, "baz": 3, "new": 3}))
	r.DontCheckRequestMethod = true
	r.HandleGET("/", func() string {
		return "<!doctype html><p>Hello World, 中国!"
	})
	r.RunServer("0.0.0.0:8080", make(chan struct{}))
}
