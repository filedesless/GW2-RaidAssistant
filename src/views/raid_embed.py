import datetime
from discord import Color, Embed
from core.constants import COMP


class RaidEmbed(Embed):

    default_description = "Raid signup. React with the roles you wish to play"
    default_composition = "TBD"

    TEAM_COMPOSITION_FIELD_INDEX = 2
    PLAYER_ROLE_USER_FIELD_INDEX = 3
    PLAYER_ROLE_VALUE_FIELD_INDEX = 4

    default_links = COMP

    def __init__(self, raid, composition={}, player_roles={}):
        super().__init__()

        self.title = "R A I D S"
        self.type = "rich"
        self.color = Color.red()

        self.description = raid.description or self.default_description

        self.add_field(
            name='Time', value=raid.time or self.get_default_time(), inline=False)
        self.add_field(name='Raid comp',
                       value=self.default_links, inline=False)

        self.add_composition_field(composition)
        self.add_player_role_field(player_roles)

    def get_default_time(self) -> str:
        today = datetime.date.today()
        # daily reset + 1h
        t = datetime.time(hour=1, tzinfo=datetime.timezone.utc)
        for i in range(7):
            day = today + datetime.timedelta(days=i)
            if day.weekday() == 1:  # monday
                monday = int(datetime.datetime.combine(day, t).timestamp())
                break
        return f'<t:{monday}:F>'

    def set_as_calculating(self):
        self.set_field_at(self.TEAM_COMPOSITION_FIELD_INDEX, name='Team Composition',
                          value='Calculating...')

    def set_as_failed(self):
        self.set_field_at(self.TEAM_COMPOSITION_FIELD_INDEX, name='Team Composition',
                          value='Failed. Could not generate a team composition.')

    def add_composition_field(self, composition):
        if not composition:
            self.add_field(name='Team Composition', value='TBD', inline=False)
            return

        entries = [f"{role} {user}" for (user, role) in composition.items()]
        formatted_composition = '\n'.join(sorted(entries))
        self.add_field(name=f"Team Composition ({len(entries)}/10)",
                       value=formatted_composition, inline=False)

    def add_player_role_field(self, player_roles):
        if not player_roles:
            return

        for user, roles in player_roles.items():
            if "Missing player" in user:
                continue

            self.add_field(name=user, value='\u200b'.join(roles))
