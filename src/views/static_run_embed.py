from discord import Color, Embed


class StaticRunEmbed(Embed):

    default_description = "Static raid clear. React with the roles you wish to play"
    default_time = "Tuesday & Thursday @ Daily Reset + 1"
    default_composition = "TBD"

    description_template = """
        {}

        **Time**
        {}

        **Links**
        [Raid Planner](https://docs.google.com/spreadsheets/d/1FGR_MssFo2wUA4SRLYke60NKhhZr21cW60XGS1rXzhw/edit#gid=1468951831)

        **TLDR**
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

        **Team Composition**
        {}
        """

    def __init__(self, raid):
        super().__init__()

        self.title = "HoT Raid Clear"
        self.type = "rich"
        self.color = Color.red()

        self.event_description = raid.description or self.default_description
        self.event_time = raid.time or self.default_time
        self.event_composition = raid.composition or self.default_composition

        self.description = self.description_template.format(
            self.event_description, self.event_time, self.event_composition)
