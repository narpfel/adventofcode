package main

import (
	"fmt"
	"io/ioutil"
	"log"
	"strings"
)

func main() {
	input_bytes, err := ioutil.ReadFile("input")
	if err != nil {
		log.Fatal(err)
	}
	input := string(input_bytes)

	groups := strings.Split(input, "\n\n")
	total := 0
	for _, group := range groups {
		set := map[rune]struct{}{}
		for _, char := range group {
			set[char] = struct{}{}
		}
		delete(set, '\n')
		total += len(set)
	}
	fmt.Println(total)
}
