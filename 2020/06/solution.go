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

func solve(declarations [][]map[rune]struct{}, answerCounts func(int, int) bool) int {
	total := 0
	for _, group := range declarations {
		commonAnswers := map[rune]int{}
		for _, declaration := range group {
			for key, _ := range declaration {
				commonAnswers[key]++
			}
		}
		for _, count := range commonAnswers {
			if answerCounts(count, len(group)) {
				total++
			}
		}
	}
	return total
}

func main() {
	declarations := parseInput("input")
	fmt.Println(solve(declarations, func(int, int) bool { return true }))
	fmt.Println(solve(
		declarations,
		func(count, groupLength int) bool { return count == groupLength },
	))
}
