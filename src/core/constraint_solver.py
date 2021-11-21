#!/usr/bin/env python3

from functools import reduce
from typing import Dict, List
import z3

class ConstraintSolver:

    def gen_primes(self):
        """ Generate an infinite sequence of prime numbers.
            Taken from https://stackoverflow.com/questions/567222/simple-prime-number-generator-in-python
        """
        D = {}
        q = 2

        while True:
            if q not in D:
                yield q
                D[q * q] = [q]
            else:
                for p in D[q]:
                    D.setdefault(p + q, []).append(p)
                del D[q]

            q += 1

    """
    ConstraintSolver ctor

    keys: dict of how many times a given role can be chosen
    player_constraints: dict of roles players have chosen
    """
    def __init__(self, keys: Dict[str, int], player_constraints: Dict[str, str]):
        g = self.gen_primes()
        self.values_by_role: Dict[str, List[int]] = { role: [ next(g) for _ in range(count) ] for (role, count) in keys.items() }
        self.roles_by_value: Dict[int, str] = { prime: role for role, primes in self.values_by_role.items() for prime in primes }
        self.players = player_constraints
        self.solution = reduce(lambda x, y: x * y, [ prime for primes in self.values_by_role.values() for prime in primes ])

    def get_solutions(self):
        solver = z3.Solver()
        player_vars = []

        # Set a constraint where each player can only play roles they've specified
        for player, roles in self.players.items():

            player_var = z3.Int(player)
            player_vars.append(player_var)
            solver.add(z3.Or([player_var == prime for role in roles for prime in self.values_by_role[role]]))

        # Set a constraint where each role must be used exactly once
        solver.add(z3.Distinct(player_vars))
        solver.add(reduce(lambda x, y: x * y, player_vars) == self.solution)

        # Iterate over all solutions
        while True:

            if solver.check() == z3.unsat:
                print("Could not find any more valid solutions for these constraints")
                return

            model = solver.model()

            yield { str(username) : self.roles_by_value[model[username].as_long()] for username in model.decls() }

            # Add the previous solution to the list of constraints
            solver.add(z3.Or([var != model[var] for var in player_vars]))
