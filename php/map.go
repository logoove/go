package php

import "container/list"

type Element struct {
	Key, Value interface{}

	element *list.Element
}
type orderedMapElement struct {
	key, value interface{}
}

type Map2 struct {
	kv map[interface{}]*list.Element
	ll *list.List
}

func newElement(e *list.Element) *Element {
	if e == nil {
		return nil
	}

	element := e.Value.(*orderedMapElement)

	return &Element{
		element: e,
		Key:     element.key,
		Value:   element.value,
	}
}

func (e *Element) Next() *Element {
	return newElement(e.element.Next())
}

func (e *Element) Prev() *Element {
	return newElement(e.element.Prev())
}
func NewMap() *Map2 {
	return &Map2{
		kv: make(map[interface{}]*list.Element),
		ll: list.New(),
	}
}
func (m *Map2) Get(key interface{}) (interface{}, bool) {
	value, ok := m.kv[key]
	if ok {
		return value.Value.(*orderedMapElement).value, true
	}

	return nil, false
}
func (m *Map2) Set(key, value interface{}) bool {
	_, didExist := m.kv[key]

	if !didExist {
		element := m.ll.PushBack(&orderedMapElement{key, value})
		m.kv[key] = element
	} else {
		m.kv[key].Value.(*orderedMapElement).value = value
	}

	return !didExist
}
func (m *Map2) GetOrDefault(key, defaultValue interface{}) interface{} {
	if value, ok := m.kv[key]; ok {
		return value.Value.(*orderedMapElement).value
	}

	return defaultValue
}
func (m *Map2) GetElement(key interface{}) *Element {
	value, ok := m.kv[key]
	if ok {
		element := value.Value.(*orderedMapElement)
		return &Element{
			element: value,
			Key:     element.key,
			Value:   element.value,
		}
	}

	return nil
}
func (m *Map2) Len() int {
	return len(m.kv)
}
func (m *Map2) Keys() (keys []interface{}) {
	keys = make([]interface{}, m.Len())

	element := m.ll.Front()
	for i := 0; element != nil; i++ {
		keys[i] = element.Value.(*orderedMapElement).key
		element = element.Next()
	}

	return keys
}
func (m *Map2) Delete(key interface{}) (didDelete bool) {
	element, ok := m.kv[key]
	if ok {
		m.ll.Remove(element)
		delete(m.kv, key)
	}

	return ok
}
func (m *Map2) Front() *Element {
	front := m.ll.Front()
	if front == nil {
		return nil
	}

	element := front.Value.(*orderedMapElement)

	return &Element{
		element: front,
		Key:     element.key,
		Value:   element.value,
	}
}
func (m *Map2) Back() *Element {
	back := m.ll.Back()
	if back == nil {
		return nil
	}

	element := back.Value.(*orderedMapElement)

	return &Element{
		element: back,
		Key:     element.key,
		Value:   element.value,
	}
}
func (m *Map2) Copy() *Map2 {
	m2 := NewMap()

	for el := m.Front(); el != nil; el = el.Next() {
		m2.Set(el.Key, el.Value)
	}

	return m2
}
