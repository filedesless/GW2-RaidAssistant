import os
from collections import defaultdict

import discord
from discord.ext import commands

from core.constants import DEFAULT_REACTIONS, ROLE_REACTIONS
from core.constraint_solver import get_solution
from views.raid_embed import RaidEmbed

# msg_id -> (username -> [emoji])
STATE: dict[int, dict[str, set[str]]] = {}


class RaidAssistant(discord.ext.commands.Bot):

    async def get_roles_per_user(self, payload: discord.RawReactionActionEvent):
        channel = await self.fetch_channel(payload.channel_id)
        message = await channel.fetch_message(payload.message_id)

        raid_roles_per_user = defaultdict(set)
        for reaction in message.reactions:
            if str(reaction.emoji) not in ROLE_REACTIONS:
                continue

            async for user in reaction.users():
                if user.id == self.user.id:
                    continue
                raid_roles_per_user[user.name].add(str(reaction.emoji))
        print("got roles", raid_roles_per_user)
        return raid_roles_per_user

    async def on_ready(self):
        print(f"Logged in as {self.user}!")

    async def on_raw_reaction_add(self, payload: discord.RawReactionActionEvent):
        if payload.user_id == self.user.id:
            return
        channel = await self.fetch_channel(payload.channel_id)
        message = await channel.fetch_message(payload.message_id)
        if message.author.id != self.user.id:
            return
        if not payload.message_id in STATE:
            STATE[payload.message_id] = await self.get_roles_per_user(payload)
        else:
            STATE[payload.message_id][payload.member.name].add(
                str(payload.emoji))
        if len(STATE[payload.message_id]) <= 10:
            await self.find_composition(message)

    async def on_raw_reaction_remove(self, payload: discord.RawReactionActionEvent):
        if payload.user_id == self.user.id:
            return
        channel = await self.fetch_channel(payload.channel_id)
        message = await channel.fetch_message(payload.message_id)
        if message.author.id != self.user.id:
            return
        if not payload.message_id in STATE:
            STATE[payload.message_id] = await self.get_roles_per_user(payload)
        user = await self.fetch_user(payload.user_id)
        if str(payload.emoji) in STATE[payload.message_id][user.name]:
            STATE[payload.message_id][user.name].remove(str(payload.emoji))
            if not STATE[payload.message_id][user.name]:
                del STATE[payload.message_id][user.name]
            if len(STATE[payload.message_id]) <= 10:
                await self.find_composition(message)

    async def find_composition(self, message: discord.Message):
        # Find a valid composition
        embed = message.embeds[0]
        new_embed = RaidEmbed(embed.description, embed.fields[0].value)
        solution = get_solution(STATE[message.id])
        print("Found solution: ", solution)
        if solution:
            new_embed.set_team_comp(solution, STATE[message.id])
        else:
            new_embed.set_as_failed()

        await message.edit(embed=new_embed)


@commands.command(name='create')
async def create_raid(ctx, description=None, time=None):
    embed = RaidEmbed(description, time)
    message = await ctx.send("", embed=embed)

    STATE[message.id] = defaultdict(set)

    for emoji in DEFAULT_REACTIONS:
        await message.add_reaction(emoji)

if __name__ == '__main__':
    # Initialize database
    intents = discord.Intents.default()
    intents.message_content = True
    bot = RaidAssistant(command_prefix='!raid', intents=intents)

    bot.add_command(create_raid)
    bot.run(os.environ['DISCORD_BOT_TOKEN'])
