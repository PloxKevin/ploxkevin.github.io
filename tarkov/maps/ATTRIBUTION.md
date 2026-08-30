# Basemap attribution

The SVG basemaps in this directory are unmodified copies from the
[Escape from Tarkov SVG Maps Project](https://github.com/the-hideout/tarkov-dev-svg-maps)
at revision `5a8b6115d1c0cf56f2ebaac1a96fa5ae3074d178`. The project credits Shebuka
and its contributors for the interactive SVG maps.

The assets are licensed under
[CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/).
See [LICENSE.md](./LICENSE.md) for the complete license. Reuse must remain
noncommercial, provide attribution, and use the same license for adaptations.
The upstream project also expressly prohibits using these assets in cheating
software or tools intended to provide an unfair in-game advantage.

Coordinate bounds, rotations, and CRS.Simple transformations in
`../data/map-config.json` are derived from
[`src/data/maps.json`](https://github.com/the-hideout/tarkov-dev/blob/560a844649b92aba1cdd463271e21e772e4e8df9/src/data/maps.json)
in Tarkov.dev, which is distributed under the MIT License.

`Labs.svg` is used for The Lab with its `Technical_Level`, `First_Level`, and
`Second_Level` groups. Tarkov.dev's current level ranges and older
TarkovTracker metadata were used to select the floor from objective elevation.
The SVG is stretched to the current CRS bounds and the UI therefore labels the
artwork alignment **approximate**, even though the quest coordinates themselves
come directly from the seasonal data snapshot.

The Labyrinth and Icebreaker overview maps are loaded from the Official Escape
from Tarkov Wiki CDN and remain hosted by the Wiki:

- [The Labyrinth Interactive Map Base](https://escapefromtarkov.fandom.com/wiki/File:The_Labyrinth_Interactive_Map_Base.png),
  by re3mr with help from the Escape from Tarkov Wiki.
- [Icebreaker Map by re3mr](https://escapefromtarkov.fandom.com/wiki/File:Icebreaker_Map_by_re3mr.jpg),
  by re3mr.

Both maps state a CC BY-NC-SA 4.0 license in the artwork. The Labyrinth uses an
approximate affine fit against its published map coordinates. Icebreaker has no
quest coordinates in the current seasonal feed; only the seven possible/fixed
positions documented by the Wiki guides for *Peaceful Atom* and *Wiring the
Vessel* receive cyan approximate pins. All other Icebreaker objectives remain
explicitly map-level rather than being assigned invented positions. Hovered
quest images link back to their individual Wiki file pages for rights details.

Escape from Tarkov and related marks are property of Battlestate Games. This
community project is not affiliated with or endorsed by Battlestate Games.
