# Proof Repair and (Co)algebra Equivalences

E.G. Plante III, Eric Paul, Cosmo Viola, G.A. Kavvos, and Talia Ringer

- **Paper:** [`paper.pdf`](paper.pdf)
- **Agda artifact:** [`artifact/`](artifact/). See [`artifact/README.md`](artifact/README.md) for setup instructions and a map from every numbered result in the paper to its formalization.
- **Browsable HTML:** <https://prt-ema.pages.dev/>. The ✓ markers in the paper link here.

The artifact typechecks with Agda 2.7.0.1:

```
cd artifact
agda everything.agda
```

`site/` holds the rendered HTML served by Cloudflare Pages.

Released under the BSD 3-Clause license (see [`LICENSE`](LICENSE)).
