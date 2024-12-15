#!/usr/bin/env python3

EXPECTED_PART_1 = 10092
EXPECTED_PART_2 = 9021


def read_input(filename):
    with open(filename) as lines:
        warehouse, moves = lines.read().split("\n\n")

    tiles = {}
    for y, line in enumerate(warehouse.splitlines()):
        for x, c in enumerate(line.strip()):
            tiles[x, y] = c

    return tiles, [move for move in moves if move in "<>^v"]


def step(point, move):
    x, y = point
    match move:
        case "^":
            return x, y - 1
        case ">":
            return x + 1, y
        case "v":
            return x, y + 1
        case "<":
            return x - 1, y
        case _:
            raise AssertionError(f"unreachable move: {move!r}")


def part_1(puzzle_input):
    tiles, moves = puzzle_input
    tiles = dict(tiles)
    x, y = next(p for p, tile in tiles.items() if tile == "@")

    for move in moves:
        position = move_target = step((x, y), move)
        while True:
            match tiles[position]:
                case "#":
                    break
                case ".":
                    tiles[x, y] = "."
                    tiles[position] = "O"
                    tiles[move_target] = "@"
                    x, y = move_target
                    break
                case "O":
                    position = step(position, move)

    return sum(
        100 * y + x
        for (x, y), tile in tiles.items()
        if tile == "O"
    )


class Tile:
    def undo(self):
        pass

    def commit(self):
        pass

    def try_move(self, move, why):
        raise NotImplementedError


class Empty(Tile):
    def try_move(self, move, why):
        return True


class Wall(Tile):
    def try_move(self, move, why):
        return False


class Robot(Tile):
    def try_move(self, move, why):
        return True


class Box(Tile):
    def __init__(self, tiles, x, y):
        self.tiles = tiles
        self.position = x, y
        self.connected = []
        self.pending_position = None
        self.pending_move = None

    @property
    def x(self):
        return self.position[0]

    @property
    def y(self):
        return self.position[1]

    def undo(self):
        for connected in self.connected:
            connected.undo()
        self.connected = []
        self.pending_position = None
        self.pending_move = None

    def commit(self):
        for connected in self.connected:
            connected.commit()
        self.connected = []
        if self.pending_position is None:
            return
        x, y = self.pending_position
        self.tiles[self.position] = Empty()
        self.tiles[self.x + 1, self.y] = Empty()
        self.tiles[x, y] = self
        self.tiles[x + 1, y] = self
        self.position = self.pending_position
        self.pending_position = None
        self.pending_move = None

    def try_move(self, move, why):
        assert self.pending_move is None or self.pending_move == move
        self.pending_move = move

        if why is not None:
            why.connected.append(self)

        assert self.pending_position is None or self.pending_position == step(self.position, move)
        self.pending_position = step(self.position, move)

        if move in "^v":
            return self.try_move_up_down(move)
        else:
            return self.try_move_left_right(move)

    def try_move_up_down(self, move):
        x, y = self.pending_position
        left_tile = self.tiles[x, y]
        right_tile = self.tiles[x + 1, y]
        if left_tile is right_tile:
            return left_tile.try_move(move, self)
        else:
            return left_tile.try_move(move, self) and right_tile.try_move(move, self)

    def try_move_left_right(self, move):
        return self._try_move_left_right_at(move, self.pending_position)

    def _try_move_left_right_at(self, move, at):
        tile = self.tiles[at]
        if tile is self:
            return self._try_move_left_right_at(move, step(self.pending_position, move))
        else:
            return tile.try_move(move, self)


def widen(tiles, tile, x, y):
    match tile:
        case "#":
            return Wall(), Wall()
        case "O":
            box = Box(tiles, 2 * x, y)
            return box, box
        case ".":
            return Empty(), Empty()
        case "@":
            return Robot(), Empty()


def part_2(puzzle_input):
    tiles, moves = puzzle_input
    items = tiles.items()
    tiles = {}
    for (x, y), tile in items:
        tiles[2 * x, y], tiles[2 * x + 1, y] = widen(tiles, tile, x, y)

    position = next(p for p, tile in tiles.items() if isinstance(tile, Robot))

    for move in moves:
        target_position = step(position, move)
        tile = tiles[target_position]
        if tile.try_move(move, None):
            tile.commit()
            tiles[position] = Empty()
            tiles[target_position] = Robot()
            position = target_position
        else:
            tile.undo()

    return sum(
        100 * y + x
        for (x, y), tile in tiles.items()
        if isinstance(tile, Box) and tile.x == x
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1
    puzzle_input = read_input("input_test_2")
    assert part_1(puzzle_input) == 2028


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    puzzle_input = read_input("input")
    print(part_1(puzzle_input))
    print(part_2(puzzle_input))


if __name__ == "__main__":
    main()
