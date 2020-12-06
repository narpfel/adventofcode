package main

import (
	"fmt"
	"io/ioutil"
	"log"
	"strings"
)

func parseInput(filename string) [][]map[rune]struct{} {
	input_bytes, err := ioutil.ReadFile("input")
	if err != nil {
		log.Fatal(err)
	}
	input := strings.TrimSpace(string(input_bytes))

	declarations := [][]map[rune]struct{}{}
	for _, group := range strings.Split(input, "\n\n") {
		declaration := []map[rune]struct{}{}
		for _, line := range strings.Split(group, "\n") {
			set := map[rune]struct{}{}
			for _, char := range line {
				set[char] = struct{}{}
			}
			declaration = append(declaration, set)
		}
		declarations = append(declarations, declaration)
	}
	return declarations
}

func part1(declarations [][]map[rune]struct{}) int {
	total := 0
	for _, group := range declarations {
		commonAnswers := map[rune]struct{}{}
		for _, declaration := range group {
			for key, _ := range declaration {
				commonAnswers[key] = struct{}{}
			}
		}
		total += len(commonAnswers)
	}
	return total
}

func part2(declarations [][]map[rune]struct{}) int {
	total := 0
	for _, group := range declarations {
		commonAnswers := map[rune]int{}
		for _, declaration := range group {
			for key, _ := range declaration {
				commonAnswers[key]++
			}
		}
		for _, count := range commonAnswers {
			if count == len(group) {
				total++
			}
		}
	}
	return total
}

func main() {
	declarations := parseInput("input")
	fmt.Println(part1(declarations))
	fmt.Println(part2(declarations))
}
