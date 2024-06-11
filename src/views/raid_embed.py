import datetime
from discord import Color, Embed
from core.constants import COMP, ROLE_REACTIONS


class RaidEmbed(Embed):

    TEAM_COMPOSITION_FIELD_INDEX = 2

    def __init__(self, description: str | None = None, time: str | None = None):
        super().__init__()

        self.title = "R A I D S"
        self.type = "rich"
        self.color = Color.red()

        self.description = description or "Raid signup. React with the roles you wish to play"

        time = time or self.get_default_time()
        self.add_field(name='Time', value=time, inline=False)
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

    def get_default_time(self) -> str:
        today = datetime.date.today()
        # daily reset + 30m
        t = datetime.time(minute=30, tzinfo=datetime.timezone.utc)
        for i in range(7):
            day = today + datetime.timedelta(days=i)
            if day.weekday() == 0:  # monday
                monday = int(datetime.datetime.combine(day, t).timestamp())
                break
        return f'<t:{monday}:F>'

    def set_as_failed(self):
        self.set_field_at(self.TEAM_COMPOSITION_FIELD_INDEX, name='Team Composition',
                          value='Failed. Could not generate a team composition.')
