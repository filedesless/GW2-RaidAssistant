import os
from collections import defaultdict
from typing import Dict, List

import discord

from commands import create_raid
from core.constants import *
from core.constraint_solver import get_solution
from models import *
from views.raid_embed import RaidEmbed


class RaidAssistant(discord.ext.commands.Bot):

    raid_messages = {}

    async def on_ready(self):
        print(f"Logged in as {self.user}!")

    # returns players' chosen roles (username -> [emoji])
    async def get_user_raid_roles(self, message) -> Dict[str, List[str]]:
        raid_roles_per_user = defaultdict(list)
        for reaction in message.reactions:
            if str(reaction.emoji) not in ROLE_REACTIONS:
                continue

            async for user in reaction.users():
                if user.id == self.user.id:
                    continue

                raid_roles_per_user[user.name] += [str(reaction.emoji)]

        return raid_roles_per_user

    async def on_raw_reaction_add(self, payload):

        if payload.user_id == self.user.id:
            return

        raid: Raid = Raid.get_or_none(Raid.message_id == payload.message_id)
        if not raid:
            return

        if raid.static:
            if payload.emoji.name == SUBMIT_REACTION:
                await self.find_composition(payload)
        else:
            if payload.emoji.name == ALARM_CLOCK and raid.organiser_id == str(payload.user_id):
                await self.wakeup(payload)

    async def find_composition(self, payload):
        channel = await self.fetch_channel(payload.channel_id)
        message = await channel.fetch_message(payload.message_id)
        curr_raid_info = Raid.get_or_none(Raid.message_id == message.id)

        # Intermediate loading message
        new_embed = RaidEmbed(curr_raid_info)
        new_embed.set_as_calculating()
        await message.edit(embed=new_embed)

        # Find a valid composition
        raid_roles_per_user: Dict[str, str] = await self.get_user_raid_roles(message)
        solution = get_solution(raid_roles_per_user)
        if solution:
            print("Found solution: ", solution)
            new_embed = RaidEmbed(
                curr_raid_info, solution, raid_roles_per_user)
        else:
            new_embed.set_as_failed()

        await message.edit(embed=new_embed)
        curr_raid_info.save()


if __name__ == '__main__':
    # Initialize database
    BaseModel.create_table(Raid)

    intents = discord.Intents.default()
    intents.message_content = True
    bot = RaidAssistant(command_prefix='!raid ', intents=intents)

    bot.add_command(create_raid)
    bot.run(os.environ['DISCORD_BOT_TOKEN'])
