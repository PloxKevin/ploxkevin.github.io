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

`Labs.svg` is vendored for provenance and future calibration only. Tarkov.dev
does not associate it with the current interactive The Lab transform, so the
configuration deliberately gives The Lab no image. The Lab and The Labyrinth
remain explicit unsupported-basemap entries and must not be spatially aligned
to these transforms without separate calibration.

Escape from Tarkov and related marks are property of Battlestate Games. This
community project is not affiliated with or endorsed by Battlestate Games.
