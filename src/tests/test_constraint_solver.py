import unittest
from collections import OrderedDict
from pprint import pp

from core.constraint_solver import get_solution
from core.constants import EMOJI_AHEAL, EMOJI_QHEAL, EMOJI_QDPS


class TestConstraintSolver(unittest.TestCase):

    def test_get_solution(self):
        players = OrderedDict([
            ('player0', {'⚔️'}),
            ('player1', {'⚔️'}),
            ('player2', {'⚔️'}),
            ('player3', {'⚔️'}),
            ('player4', {'⚔️'}),
            ('player5', {'⚔️'}),
            ('player6', {'⚔️'}),
            ('player7', {'⚔️'}),
            ('player8', {'⚔️'}),
            ('player9', {'⚔️'}),
            ('late gamer0', {'⚔️', EMOJI_AHEAL}),
            ('late gamer1', {'⚔️', EMOJI_QHEAL}),
            ('late gamer2', {'⚔️'}),
            ('late gamer3', {'⚔️', EMOJI_AHEAL, EMOJI_QDPS}),
            ('late gamer4', {'⚔️', EMOJI_AHEAL}),
        ])

        # imagine asserting
        pp(sorted(get_solution(players).items(), key=lambda p: p[0]))


if __name__ == '__main__':
    unittest.main()
