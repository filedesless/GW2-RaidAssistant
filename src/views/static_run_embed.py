from discord import Color, Embed


class StaticRunEmbed(Embed):

    default_description = "Static raid clear. React with the roles you wish to play"
    default_time = "Tuesday & Thursday @ Daily Reset + 1"
    default_composition = "TBD"

    TEAM_COMPOSITION_FIELD_INDEX = 2
    PLAYER_ROLE_USER_FIELD_INDEX = 3
    PLAYER_ROLE_VALUE_FIELD_INDEX = 4

    default_links = """
        [Raid Planner](https://docs.google.com/spreadsheets/d/1FGR_MssFo2wUA4SRLYke60NKhhZr21cW60XGS1rXzhw/)
    """

    def __init__(self, raid, composition={}, player_roles={}):
        super().__init__()

        self.title = "HoT Raid Clear"
        self.type = "rich"
        self.color = Color.red()

        self.description = raid.description or self.default_description

        self.add_field(name='Time', value=raid.time or self.default_time, inline=False)
        self.add_field(name='Links', value=self.default_links, inline=False)

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
        for key, user in composition.items():
            if "Missing player" in user:
                user = ""

            entries += ["{} {}".format(key, user)]

        formatted_composition = '\n'.join(sorted(entries))
        self.add_field(name='Team Composition', value=formatted_composition, inline=False)


    def add_player_role_field(self, player_roles):
        if not player_roles:
            return

        for user, roles in player_roles.items():
            if "Missing player" in user:
                continue

            self.add_field(name=user, value='\u200b'.join(roles))