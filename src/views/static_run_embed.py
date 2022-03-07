from discord import Color, Embed
from core.constants import COMP


class StaticRunEmbed(Embed):

    default_description = "Static raid clear. React with the roles you wish to play"
    default_time = "Tuesday & Thursday @ Daily Reset + 2"
    default_composition = "TBD"

    TEAM_COMPOSITION_FIELD_INDEX = 2
    PLAYER_ROLE_USER_FIELD_INDEX = 3
    PLAYER_ROLE_VALUE_FIELD_INDEX = 4

    default_links = f"""
        {COMP}
        Details [online](https://github.com/afrigon/tlwk#readme)
    """

    def __init__(self, raid, composition={}, player_roles={}):
        super().__init__()

        self.title = "HoT Raid Clear"
        self.type = "rich"
        self.color = Color.red()

        self.description = raid.description or self.default_description

        self.add_field(
            name='Time', value=raid.time or self.default_time, inline=False)
        self.add_field(name='Raid comp',
                       value=self.default_links, inline=False)

        self.add_composition_field(composition)
        self.add_player_role_field(player_roles)

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

        entries = []
        scourge_icon = ""
        scourges = []
        for user, role in composition.items():
            if "Missing player" in user:
                user = ""
            if "necro_scourge" in role:
                scourge_icon = role
                if len(user) > 0:
                    scourges += [user]
            else:
                entries += ["{} {}".format(role, user)]

        formatted_composition = '\n'.join(sorted(entries))
        formatted_composition = "{}\n{} {}".format(
            formatted_composition, scourge_icon, ", ".join(scourges))
        n = len([user for user in composition.keys()
                if "Missing player" not in user])
        self.add_field(name="Team Composition ({}/10)".format(n),
                       value=formatted_composition, inline=False)

    def add_player_role_field(self, player_roles):
        if not player_roles:
            return

        for user, roles in player_roles.items():
            if "Missing player" in user:
                continue

            self.add_field(name=user, value='\u200b'.join(roles))
