#!/usr/bin/env python3
import sys
from operator import attrgetter

import attr


@attr.s(frozen=True)
class Vector:
    x = attr.ib()
    y = attr.ib()

    def __lt__(self, other):
        if not isinstance(other, type(self)):
            return NotImplemented
        return (self.y, self.x) < (other.y, other.x)

    def __add__(self, other):
        return type(self)(self.x + other.x, self.y + other.y)


TURNS = [
    lambda direction: Vector(direction.y, -direction.x),
    lambda direction: direction,
    lambda direction: Vector(-direction.y, direction.x),
]

DIRECTIONS = {
    "<": Vector(-1, 0),
    ">": Vector(1, 0),
    "^": Vector(0, -1),
    "v": Vector(0, 1),
}

DIRECTION_TO_SYMBOL = {position: symbol for symbol, position in DIRECTIONS.items()}

CARTS = frozenset(DIRECTIONS)

CART_TO_TILE = {
    "<": "-",
    ">": "-",
    "^": "|",
    "v": "|",
}

CORNERS = {
    ("/", DIRECTIONS["<"]): DIRECTIONS["v"],
    ("/", DIRECTIONS[">"]): DIRECTIONS["^"],
    ("/", DIRECTIONS["^"]): DIRECTIONS[">"],
    ("/", DIRECTIONS["v"]): DIRECTIONS["<"],
    ("\\", DIRECTIONS["<"]): DIRECTIONS["^"],
    ("\\", DIRECTIONS[">"]): DIRECTIONS["v"],
    ("\\", DIRECTIONS["^"]): DIRECTIONS["<"],
    ("\\", DIRECTIONS["v"]): DIRECTIONS[">"],
}


@attr.s
class Cart:
    position = attr.ib()
    direction = attr.ib()
    turn_count = attr.ib(default=0)
    dead = attr.ib(default=False)

    @property
    def symbol(self):
        return DIRECTION_TO_SYMBOL[self.direction]

    def move(self, tiles):
        self.position += self.direction
        if is_corner(tiles[self.position]):
            self.direction = TURNS[self.turn_count % len(TURNS)](self.direction)
            self.turn_count += 1
        self.direction = CORNERS.get((tiles[self.position], self.direction), self.direction)

    def collides_with(self, carts):
        return any(cart is not self and cart.position == self.position for cart in carts)


def is_corner(tile):
    return tile == "+"


def simulate(tiles, carts, visualise):
    while True:
        for cart in sorted(carts, key=attrgetter("position")):
            if visualise:
                show(tiles, carts)
            if cart.dead:
                continue
            cart.move(tiles)
            if cart.collides_with(carts):
                yield cart.position
                for c in carts:
                    if c.position == cart.position:
                        c.dead = True

        carts = [cart for cart in carts if not cart.dead]

        if len(carts) == 1:
            yield carts[0].position
            return


def show(tiles, carts):
    # TODO: Only draw `tiles` once to reduce cart flickering.
    for position, tile in tiles.items():
        print(f"\x1B[{position.y + 1};{position.x + 1}H{tile}", end="")
    for cart in carts:
        print(f"\x1B[{cart.position.y + 1};{cart.position.x + 1}H{cart.symbol}", end="")
    print(end="", flush=True)


def main():
    visualise = sys.argv[1:] == ["--visualise"]

    with open("input") as lines:
        tiles = {
            Vector(x, y): tile
            for y, line in enumerate(lines)
            for x, tile in enumerate(line)
        }

    carts = [
        Cart(position, DIRECTIONS[tile])
        for (position, tile) in tiles.items()
        if tile in CARTS
    ]
    tiles = {position: CART_TO_TILE.get(tile, tile) for (position, tile) in tiles.items()}

    try:
        if visualise:
            print("\x1B[?25l\x1B[2J", end="")

        end_positions = list(simulate(tiles, carts, visualise))

        if visualise:
            print("\x1B[2J\x1B[H", end="")

        print(f"{end_positions[0].x},{end_positions[0].y}")
        print(f"{end_positions[-1].x},{end_positions[-1].y}")
    finally:
        if visualise:
            print("\x1B[?25h", end="", flush=True)


if __name__ == "__main__":
    main()
