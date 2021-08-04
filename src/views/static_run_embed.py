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

        TLDR:
        \U0001f1e6 Tankbrand
        \U0001f1e7 Spiritbeast/HK
        \U0001f1e8 Alacren
        \U0001f1e9 Banners
        \U0001f1ea Scourge
        \U0001f1eb Engi
        \U0001f1ec Thief
        \U0001f1ed Mesmer
        \U0001f1ee Boon Heal Temp
        \U0001f1ef Scourge
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
        self.set_field_at(self.PLAYER_ROLE_USER_FIELD_INDEX, name='Player Roles', value='\u200b')
        self.set_field_at(self.PLAYER_ROLE_VALUE_FIELD_INDEX, name='\u200b', value='\u200b')

    def set_as_failed(self):
        self.set_field_at(self.TEAM_COMPOSITION_FIELD_INDEX, name='Team Composition',
                value='Failed. Could not generate a team composition.')

    def add_composition_field(self, composition):
        if not composition:
            self.add_field(name='Team Composition', value='TBD')
            return

        entries = []
        for key, user in composition.items():
            if "Missing player" in user:
                user = ""

            entries += ["{} {}".format(key, user)]

        formatted_composition = '\n'.join(sorted(entries))
        self.add_field(name='Team Composition', value=formatted_composition)


    def add_player_role_field(self, player_roles):
        if not player_roles:
            self.add_field(name='Player Roles', value='\u200b')
            self.add_field(name='\u200b', value='\u200b')
            return

        player_names = []
        formatted_player_roles = []
        for user, roles in player_roles.items():
            if "Missing player" in user:
                continue

            player_names += [user]
            formatted_player_roles += ['\u200b'.join(roles)]

        self.add_field(name='Player Roles', value='\n'.join(player_names))
        self.add_field(name='\u200b', value='\n'.join(formatted_player_roles))

