#!/usr/bin/env python3

from typing import Dict, List, Optional
from core.constants import ROLE_REACTIONS
import z3


def get_solution(players: Dict[str, List[str]]) -> Optional[Dict[str, str]]:
    """Returns the optimal solution found {name: role} if any

    Args: 
        players: association of player names and roles they wish to play {name: [role]}
    """
    solver = z3.Optimize()
    player_vars = []

    # Set a constraint where each player can only play any of the roles they've specified
    for name, roles in players.items():
        # A player_var is an integer that represents the class a player will be playing
        player_var = z3.Int(name)
        solver.add(z3.And(player_var >= 0, player_var < len(ROLE_REACTIONS)))
        player_vars.append(player_var)
        solver.add(z3.Or([player_var == ROLE_REACTIONS.index(role) for role in roles]))

    # at most 2 heal
    solver.add(z3.AtMost(*[z3.Or(var == 0, var == 2) for var in player_vars], 2))
    # at most 2 xdps
    solver.add(z3.AtMost(*[z3.Or(var == 1, var == 3) for var in player_vars], 2))
    # at most 2 alac
    solver.add(z3.AtMost(*[z3.Or(var == 0, var == 3) for var in player_vars], 2))
    # at most 2 quick
    solver.add(z3.AtMost(*[z3.Or(var == 1, var == 2) for var in player_vars], 2))
    # at most 6 dps
    solver.add(z3.AtMost(*[var == 4 for var in player_vars], 6))

    # Optimize for the minimal sum of player_vars, so that supports get filled first
    solver.minimize(z3.Sum(player_vars))

    # If a solution satisfying the given constraints is found, return it
    if solver.check() == z3.sat:
        model = solver.model()
        return {str(name): ROLE_REACTIONS[model[name].as_long()] for name in model.decls()}
    print("Could not find any solution")
