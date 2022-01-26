#!/usr/bin/env python3

from typing import Dict, List, Optional
from core.constants import VALUES_BY_ROLE
import z3


def role_by_value(value: int) -> Optional[str]:
    for role, values in VALUES_BY_ROLE.items():
        if value in values:
            return role


def get_solution(players: Dict[str, List[str]]) -> Optional[Dict[str, str]]:
    """Returns the optimal solution found {name: role} if any

    Args: 
        players: association of player names and roles they wish to play {name: [role]}
    """
    solver = z3.Optimize()
    player_vars = []

    # Set a constraint where each player can only play any of the roles they've specified
    for name, roles in players.items():
        # A player_var is a number in range(10) that represents the class a player will be playing
        player_var = z3.Int(name)
        solver.add(z3.And(player_var >= 0, player_var < 10))
        player_vars.append(player_var)
        solver.add(z3.Or(
            [player_var == value for role in roles for value in VALUES_BY_ROLE[role]]))

    # Set a constraint where each role must be used exactly once
    solver.add(z3.Distinct(player_vars))

    # Optimize for the maximal sum of player_vars, so that classes with a higher value get filled in priority
    solver.maximize(z3.Sum(player_vars))

    # If a solution satisfying the given constraints is found, return it
    if solver.check() == z3.sat:
        model = solver.model()
        return {str(name): role_by_value(model[name].as_long()) for name in model.decls()}
    print("Could not find any solution")
