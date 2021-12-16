#!/usr/bin/env python3

from math import prod
from operator import eq
from operator import gt
from operator import lt

import pytest
from attr import attrib
from attr import attrs


@attrs
class Literal:
    version = attrib()
    type_id = attrib()
    value = attrib()

    @property
    def version_sum(self):
        return self.version


@attrs
class Operator:
    version = attrib()
    type_id = attrib()
    sub_packets = attrib()

    @property
    def value(self):
        return {
            0: sum,
            1: prod,
            2: min,
            3: max,
            5: uncurry(gt),
            6: uncurry(lt),
            7: uncurry(eq),
        }[self.type_id](packet.value for packet in self.sub_packets)

    @property
    def version_sum(self):
        return self.version + sum(packet.version_sum for packet in self.sub_packets)


def uncurry(f):
    def uncurried_f(args):
        return f(*args)
    return uncurried_f


def to_int(bits):
    return int("".join(map(str, bits)), base=2)


def parse_transmission(transmission):
    bit_length = len(transmission) * 4
    transmission = int(transmission, base=16)
    bits = []
    for _ in range(bit_length):
        bits.append(transmission & 1)
        transmission >>= 1
    assert transmission == 0
    bits.reverse()

    i = 0

    def read(n):
        nonlocal i
        value = to_int(bits[i:i+n])
        i += n
        return value

    def parse_packet():
        version = read(3)
        type_id = read(3)
        if type_id == 4:
            value = 0
            while True:
                last_group = read(1) == 0
                value <<= 4
                value |= read(4)
                if last_group:
                    return Literal(version, type_id, value)
        else:
            length_type_id = read(1)
            if length_type_id == 0:
                total_length = read(15)
                end = i + total_length
                sub_packets = []
                while i < end:
                    sub_packets.append(parse_packet())
                return Operator(version, type_id, sub_packets)
            else:
                sub_packet_count = read(11)
                sub_packets = []
                for _ in range(sub_packet_count):
                    sub_packets.append(parse_packet())
                return Operator(version, type_id, sub_packets)

    return parse_packet()


def test_parse_literal():
    assert parse_transmission("D2FE28") == Literal(version=6, type_id=4, value=2021)


@pytest.mark.parametrize(
    "transmission, expected", [
        ("D2FE28", 6),
        ("38006F45291200", 0b001 + 0b110 + 0b010),
        ("EE00D40C823060", 0b111 + 0b010 + 0b100 + 0b001),
        ("8A004A801A8002F478", 16),
        ("620080001611562C8802118E34", 12),
        ("C0015000016115A2E0802F182340", 23),
        ("A0016C880162017C3686B18A3D4780", 31),
    ],
)
def test_parse_version_sum(transmission, expected):
    assert parse_transmission(transmission).version_sum == expected


@pytest.mark.parametrize(
    "transmission, expected", [
        ("C200B40A82", 3),
        ("04005AC33890", 54),
        ("880086C3E88112", 7),
        ("CE00C43D881120", 9),
        ("D8005AC2A8F0", 1),
        ("F600BC2D8F", 0),
        ("9C005AC2F8F0", 0),
        ("9C0141080250320F1802104A08", 1),
    ],
)
def test_evaluate(transmission, expected):
    assert parse_transmission(transmission).value == expected


def main():
    with open("input") as file:
        transmission = file.read().strip()

    packet = parse_transmission(transmission)
    print(packet.version_sum)
    print(packet.value)


if __name__ == "__main__":
    main()
