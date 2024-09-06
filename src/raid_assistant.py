import os
from collections import OrderedDict

import discord
from discord.ext import commands

from core.constants import *
from core.constraint_solver import get_solution
from views.raid_embed import RaidEmbed

# msg_id -> (int -> (name, {emoji}))
STATE: dict[int, OrderedDict[int, tuple[str, set[str]]]] = {}

class RaidAssistant(commands.Bot):

    async def get_roles_per_user(self, payload: discord.RawReactionActionEvent):
        """Fetch discord for the reactions of a non-cached message"""
        print("fetching roles")
        channel = await self.fetch_channel(payload.channel_id)
        message = await channel.fetch_message(payload.message_id)

        raid_roles_per_user = OrderedDict()
        for reaction in message.reactions:
            emoji= str(reaction.emoji)
            if emoji not in ROLE_REACTIONS:
                continue

            async for user in reaction.users():
                if not self.user or user.id == self.user.id:
                    continue
                raid_roles_per_user.setdefault(user.id, (user.name, set()))[1].add(emoji)
        print("got roles", raid_roles_per_user)
        return raid_roles_per_user

    async def on_ready(self):
        print(f"Logged in as {self.user}!")

    async def on_raw_reaction_add(self, payload: discord.RawReactionActionEvent):
        if not self.user or not payload.member or payload.user_id == self.user.id:
            return
        channel = await self.fetch_channel(payload.channel_id)
        message = await channel.fetch_message(payload.message_id)
        if message.author.id != self.user.id:
            return
        emoji = payload.emoji.name
        user = payload.member
        if not message.id in STATE:
            STATE[message.id] = await self.get_roles_per_user(payload)
        elif emoji in ROLE_REACTIONS:
            STATE[message.id].setdefault(user.id, (user.name, set()))[1].add(emoji)
        if emoji in ROLE_REACTIONS:
            await self.find_composition(message)
        if emoji == EMOJI_CLOCK:
            source = f"<@{payload.member.id}>"
            mentions = ",".join(f"<@{uid}>" for uid in STATE[message.id])
            await channel.send(f"{source}: wake up buttercups we raidin {mentions}")

    async def on_raw_reaction_remove(self, payload: discord.RawReactionActionEvent):
        if not self.user or payload.user_id == self.user.id:
            return
        channel = await self.fetch_channel(payload.channel_id)
        message = await channel.fetch_message(payload.message_id)
        if message.author.id != self.user.id:
            return
        if not payload.message_id in STATE:
            STATE[message.id] = await self.get_roles_per_user(payload)
        user = await self.fetch_user(payload.user_id)
        emoji = payload.emoji.name
        if emoji in ROLE_REACTIONS:
            if user.id in STATE[message.id] and emoji in STATE[message.id][user.id][1]:
                STATE[payload.message_id][user.id][1].remove(emoji)
                if not STATE[payload.message_id][user.id][1]:
                    del STATE[payload.message_id][user.id]
                await self.find_composition(message)

    async def find_composition(self, message: discord.Message):
        # Find a valid composition
        embed = message.embeds[0]
        new_embed = RaidEmbed(embed.description, embed.fields[0].value)
        player_roles = OrderedDict(STATE[message.id].values())
        print("player roles:", player_roles)
        if player_roles:
            solution = get_solution(player_roles)
            print("Found solution: ", solution)
            solution = { user: str(discord.utils.get(message.guild.emojis, name=solution[user])) for user in solution}
            print("fixed solution: ", solution)
            if solution:
                player_roles = {player: {str(discord.utils.get(message.guild.emojis, name=name) if name in CUSTOM_REACTIONS else name) for name in player_roles[player]} for player in player_roles}
                print("fixed player roles", player_roles)
                new_embed.set_team_comp(solution, player_roles)
            else:
                new_embed.set_as_failed()

        await message.edit(embed=new_embed)


@commands.command(name='create')
async def create_raid(ctx, description=None, time=None):
    embed = RaidEmbed(description, time)
    message = await ctx.send("", embed=embed)

    STATE[message.id] = OrderedDict()

    for name in CUSTOM_REACTIONS:
        print(name)
        emoji = discord.utils.get(ctx.guild.emojis, name=name)
        print(emoji)
        await message.add_reaction(str(emoji))
    await message.add_reaction(EMOJI_DPS)
    await message.add_reaction(EMOJI_CLOCK)

if __name__ == '__main__':
    # Initialize database
    intents = discord.Intents.default()
    intents.message_content = True
    bot = RaidAssistant(command_prefix='!', intents=intents)

    bot.add_command(create_raid)
    bot.run(os.environ['DISCORD_BOT_TOKEN'])
