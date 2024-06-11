#!/usr/bin/env python3

from collections import OrderedDict
from core.constants import ROLE_REACTIONS
import z3


def get_solution(players: OrderedDict[str, set[str]]) -> dict[str, str] | None:
    """Returns the optimal solution found {name: role} if any

    Args: 
        players: association of player names and roles they wish to play {name: [role]}
    """

    solver = z3.Optimize()
    player_vars = []

    ROLES = ROLE_REACTIONS + [":clown:"]

    # Set a constraint where each player can only play any of the roles they've specified
    for name, roles in players.items():
        # A player_var is an integer that represents the role a player will be playing
        player_var = z3.Int(name)
        solver.add(z3.And(player_var >= 0, player_var < len(ROLES) + 1))
        player_vars.append(player_var)
        solver.add(z3.Or([player_var == ROLES.index(role) for role in roles | {":clown:"}]))

    # at most 2 heal
    solver.add(z3.AtMost(*[z3.Or(var == 0, var == 2)
               for var in player_vars], 2))
    # at most 2 xdps
    solver.add(z3.AtMost(*[z3.Or(var == 1, var == 3)
               for var in player_vars], 2))
    # at most 2 alac
    solver.add(z3.AtMost(*[z3.Or(var == 0, var == 3)
               for var in player_vars], 2))
    # at most 2 quick
    solver.add(z3.AtMost(*[z3.Or(var == 1, var == 2)
               for var in player_vars], 2))
    # at most 6 dps
    solver.add(z3.AtMost(*[var == 4 for var in player_vars], 6))

    # Optimize for the minimal sum of player_vars, so that supports get filled first
    solver.minimize(z3.Sum(player_vars))

    # Optimize secondly for the minimal sum of taken player by prio, first in first serve
    # this assumes the given players dict is ordered by react time
    solver.minimize(z3.Sum([i * (var < len(ROLES) - 1)
                    for (i, var) in enumerate(player_vars)]))

    # If a solution satisfying the given constraints is found, return it
    if solver.check() == z3.sat:
        model = solver.model()
        return {str(name): ROLES[model[name].as_long()] for name in model.decls()}
    print("Could not find any solution")
