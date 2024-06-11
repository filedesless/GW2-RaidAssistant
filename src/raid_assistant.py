import os
from collections import defaultdict

import discord
from discord.ext import commands

from core.constants import DEFAULT_REACTIONS, ROLE_REACTIONS, EMOJI_CLOCK
from core.constraint_solver import get_solution
from views.raid_embed import RaidEmbed

# msg_id -> (username -> [emoji])
STATE: dict[int, dict[discord.User, set[str]]] = {}


class RaidAssistant(discord.ext.commands.Bot):

    async def get_roles_per_user(self, payload: discord.RawReactionActionEvent):
        """Fetch discord for the reactions of a non-cached message"""
        print("fetching roles")
        channel = await self.fetch_channel(payload.channel_id)
        message = await channel.fetch_message(payload.message_id)

        raid_roles_per_user = defaultdict(set)
        for reaction in message.reactions:
            if str(reaction.emoji) not in ROLE_REACTIONS:
                continue

            async for user in reaction.users():
                if user.id == self.user.id:
                    continue
                raid_roles_per_user[user].add(str(reaction.emoji))
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
        emoji = str(payload.emoji)
        if not message.id in STATE:
            STATE[message.id] = await self.get_roles_per_user(payload)
        elif emoji in ROLE_REACTIONS:
            STATE[message.id][payload.member].add(emoji)
        if emoji in ROLE_REACTIONS:
            await self.find_composition(message)
        if emoji == EMOJI_CLOCK:
            source = f"<@{payload.member.id}>"
            mentions = ",".join(f"<@{user.id}>" for user in STATE[message.id])
            await channel.send(f"{source}: wake up buttercups we raidin {mentions}")

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
        emoji = str(payload.emoji)
        if emoji and ROLE_REACTIONS and emoji in STATE[payload.message_id][user]:
            STATE[payload.message_id][user].remove(emoji)
            if not STATE[payload.message_id][user]:
                del STATE[payload.message_id][user]
            await self.find_composition(message)

    async def find_composition(self, message: discord.Message):
        # Find a valid composition
        embed = message.embeds[0]
        new_embed = RaidEmbed(embed.description, embed.fields[0].value)
        player_roles = {
            player.name: STATE[message.id][player] for player in STATE[message.id]}
        solution = get_solution(player_roles)
        print("Found solution: ", solution)
        if solution:
            new_embed.set_team_comp(solution, player_roles)
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
    await message.add_reaction(EMOJI_CLOCK)

if __name__ == '__main__':
    # Initialize database
    intents = discord.Intents.default()
    intents.message_content = True
    bot = RaidAssistant(command_prefix='!', intents=intents)

    bot.add_command(create_raid)
    bot.run(os.environ['DISCORD_BOT_TOKEN'])
