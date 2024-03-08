from itertools import product

import numpy as np
from more_itertools import unique_everseen
from scipy.spatial.transform import Rotation


def main():
    rotations = list(
        unique_everseen(
            (
                np.rint(rotation.as_matrix()).astype(int)
                for rotation in [
                    Rotation.from_euler("xyz", [90 * x, 90 * y, 90 * z], degrees=True)
                    for x, y, z in product(range(4), repeat=3)
                ]
            ),
            key=lambda rotation: tuple(map(tuple, rotation)),
        ),
    )

    print([
        list(zip(np.argmax(rotation != 0, axis=1), np.sum(rotation, axis=1)))
        for rotation in rotations
    ])


if __name__ == "__main__":
    main()
