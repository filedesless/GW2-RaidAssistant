from datetime import UTC, datetime, timedelta, time
from discord import Color, Embed
from core.constants import COMP, ROLE_REACTIONS


MON, TUE, WED, THU, FRI, SAT, SUN = range(7)


class RaidEmbed(Embed):

    TEAM_COMPOSITION_FIELD_INDEX = 2

    def __init__(self, description: str | None = None, event_time: str | None = None):
        super().__init__()

        self.title = "R A I D S"
        self.type = "rich"
        self.color = Color.red()

        self.description = description or "Raid signup. React with the roles you wish to play"

        event_time = event_time or f'<t:{int(get_next_time(day=MON, minute=30).timestamp())}:F>'
        self.add_field(name='Time', value=event_time, inline=False)
        self.add_field(name='Raid comp', value=COMP, inline=False)
        self.add_field(name='Team Composition', value='TBD', inline=False)

    def set_team_comp(self, composition: dict[str, str], player_roles: dict[str, list[str]]):
        entries = [f"{role} {user}" for (user, role) in composition.items()]
        formatted_composition = '\n'.join(sorted(entries))
        self.set_field_at(self.TEAM_COMPOSITION_FIELD_INDEX,
                          name=f"Team Composition ({len(entries)}/10)",
                          value=formatted_composition, inline=False)
        for user, roles in player_roles.items():
            self.add_field(name=user, value='\u200b'.join(
                role for role in ROLE_REACTIONS if role in roles))

    def set_as_failed(self):
        self.set_field_at(self.TEAM_COMPOSITION_FIELD_INDEX, name='Team Composition',
                          value='Failed. Could not generate a team composition.')


def get_next_time(day: int = SUN, hour: int = 0, minute: int = 0) -> datetime:
    """Finds next time day reset + hour:min occurs"""
    now = datetime.now(UTC)
    t = time(hour=hour, minute=minute, tzinfo=UTC)
    for i in range(8):
        tt = datetime.combine(now.date() + timedelta(days=i), t)
        # check next day since after reset
        if now < tt and tt.weekday() == (day + 1) % 7:
            return tt
