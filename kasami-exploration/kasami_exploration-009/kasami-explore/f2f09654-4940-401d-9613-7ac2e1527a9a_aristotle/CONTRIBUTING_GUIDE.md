# High-Leverage Ways to Contribute to Lean 4 Core & Mathlib

## The 80/20 of Contributing

### 1. Review Pull Requests (Highest Leverage, Most Needed)

**This is the single highest-leverage activity.** Mathlib has a chronic bottleneck of PRs waiting for review. A PR that sits unreviewed for weeks demoralizes contributors and slows the entire project.

- You don't need to be an expert in the area — even checking that code compiles, follows style, and has good documentation is valuable.
- Start by reviewing PRs labeled `easy` or `awaiting-review` on the Mathlib4 GitHub.
- Mathlib uses a delegated review system: once you're trusted, you can `bors delegate+` to approve PRs.
- **Why it's 80/20:** One good reviewer unblocks dozens of contributors. The ratio of PR authors to reviewers is heavily skewed.

### 2. Fix Broken CI / Build Maintenance

- Mathlib is enormous (~1.5M+ lines). When upstream Lean changes or internal refactors happen, things break.
- Fixing CI breakages, adapting to Lean toolchain bumps, and keeping `master` green is unglamorous but essential.
- **Where to look:** `#mathlib4` and `#lean4` channels on Zulip for current breakages.

### 3. Improve and Write Documentation

- Many Mathlib files have minimal or no module-level docstrings.
- Tactic documentation is often sparse — users struggle to discover what's available.
- Contributing doc-strings, module headers, and examples has outsized impact on adoption.
- The [Mathlib documentation style guide](https://leanprover-community.github.io/contribute/style.html) explains conventions.

---

## Areas With the Fewest Maintainers / Most Help Needed

### In Mathlib:

1. **Combinatorics** — Relatively undermaintained compared to its breadth. Graph theory, matroid theory, extremal combinatorics all need work.

2. **Number Theory (Analytic)** — Lots of foundational pieces are missing. L-functions, modular forms beyond basics, sieve methods.

3. **Probability Theory** — The measure-theoretic probability framework exists but is incomplete. Conditional expectation, martingales, and convergence theorems need contributors.

4. **Numerical / Computational Mathematics** — Verified numerics, interval arithmetic, computational algebra are sparsely covered.

5. **Category Theory maintenance** — The category theory library is large but has relatively few active maintainers for its size. Understanding universe polymorphism issues here is a rare skill.

6. **Topology & Geometry glue** — Connections between algebraic topology, differential geometry, and algebra are thin. Sheaf theory, cohomology, fiber bundles.

7. **Tactic maintenance** — Many tactics in `Mathlib.Tactic` have a single author-maintainer. When that person is busy, bugs and feature requests pile up.

### In Lean 4 Core:

1. **Lake (build system)** — Frequently cited as needing help. Build system work is unglamorous but affects every user.
2. **Error messages & diagnostics** — Improving error messages is always welcome and high-impact.
3. **Editor integration / LSP** — VS Code extension, language server improvements.
4. **Documentation & onboarding** — Core Lean documentation could always be clearer.

---

## Your Intuition Is Correct: Maintenance > New Theory (Usually)

You're right that **refactoring and maintenance are often more valuable than new theory**, especially for someone starting out. Here's why:

### Why Maintenance Is Higher Leverage:

- **New theory PRs are abundant** — Many mathematicians want to formalize their favorite results. The bottleneck is rarely "not enough new content."
- **Maintenance PRs are scarce** — Few people enjoy refactoring, fixing deprecation warnings, improving performance, or cleaning up technical debt. Supply is low, demand is high.
- **Refactors compound** — A good API cleanup or naming convention fix touches hundreds of downstream files and makes everyone's life easier forever.
- **You learn the codebase deeply** — Maintenance work forces you to understand how things fit together, which makes you a better reviewer and future contributor.

### High-Leverage Maintenance Tasks:

1. **`simp` lemma hygiene** — Auditing `@[simp]` tags. Bad simp lemmas slow down the entire library. Removing or fixing problematic ones is extremely valuable.

2. **Deprecation cleanup** — Removing uses of deprecated lemmas, definitions, and tactics throughout the codebase.

3. **Reducing import graphs** — Mathlib's compile times are a major pain point. Finding ways to reduce transitive imports (splitting files, reorganizing modules) directly improves every contributor's experience.

4. **Linter improvements** — Writing or improving Mathlib linters catches problems automatically for all future PRs.

5. **API gaps** — Adding missing lemmas to existing theories (e.g., `List`, `Finset`, `Multiset` missing obvious operations or equivalences). These are small PRs but unblock many downstream users.

6. **Universe polymorphism fixes** — Making definitions maximally universe-polymorphic where they currently aren't.

7. **Performance profiling** — Identifying and fixing slow elaboration, slow `simp` calls, or slow typeclass inference. Tools: `set_option profiler true`, `set_option trace.Meta.synthInstance true`.

---

## Different Ways to Contribute Value

| Activity | Impact | Barrier to Entry | Supply of Contributors |
|---|---|---|---|
| PR Review | 🔥🔥🔥 | Medium | Very Low |
| CI / Build fixes | 🔥🔥🔥 | Medium-High | Very Low |
| Tactic improvements | 🔥🔥🔥 | High | Low |
| Refactoring / API cleanup | 🔥🔥 | Medium | Low |
| Documentation | 🔥🔥 | Low | Low |
| Filing good bug reports | 🔥🔥 | Low | Medium |
| Answering Zulip questions | 🔥🔥 | Low-Medium | Medium |
| New theory development | 🔥 | Medium-High | High |
| Fixing linter warnings | 🔥🔥 | Low | Low |
| Import graph optimization | 🔥🔥🔥 | Medium | Very Low |

---

## Best Practices

### Getting Started:

1. **Join Zulip** — The [leanprover Zulip](https://leanprover.zulipchat.com/) is where all coordination happens. Lurk in `#mathlib4`, `#new members`, `#PR reviews`.

2. **Start with small PRs** — Fix a typo, add a missing lemma, improve a docstring. This gets you familiar with the PR process (which has specific conventions).

3. **Read the contribution guide** — Mathlib has detailed style and contribution guidelines. Following them from day one saves reviewer time.

4. **Claim issues on GitHub** — Look for issues labeled `good first issue` or `help wanted`.

5. **Don't work in isolation** — Before starting a large project, post on Zulip to check if someone else is working on it and to get design feedback.

### PR Best Practices:

- **Small, focused PRs** — One logical change per PR. Large PRs are hard to review and sit longer.
- **Good commit messages** — Describe *why*, not just *what*.
- **Add `@[simp]` lemmas judiciously** — Every simp lemma slows down every `simp` call. Only add them if they're genuinely useful simplification directions.
- **Follow naming conventions** — Mathlib has strict naming conventions (e.g., `theorem_name_reflects_statement`). Use `#check` to see how similar lemmas are named.
- **Include tests for tactics** — If you modify a tactic, add test cases.
- **Minimize imports** — Don't `import Mathlib` in your PR; import only what you need.

### Review Best Practices:

- **Be constructive and kind** — Many contributors are new to formal verification.
- **Check mathematical correctness** — Does the statement actually say what it claims?
- **Check API design** — Is the lemma stated in maximal generality? Are the hypotheses minimal?
- **Check naming** — Does it follow conventions?
- **Check for `sorry`** — Obviously, but also check for `Decidable.decide` abuse, `native_decide` in non-computational contexts, and other escape hatches.

---

## Concrete High-Leverage Projects Right Now

1. **Help with the `simp` audit** — There's an ongoing effort to clean up simp lemmas across Mathlib.

2. **Improve `omega` / `positivity` / `polyrith` tactics** — These automation tactics are used everywhere. Making them faster or more powerful has multiplicative impact.

3. **Work on `Mathlib.Order`** — The order theory library underpins algebra, topology, and measure theory. It's foundational but sometimes has API gaps.

4. **`Finset` / `Fintype` API completion** — Combinatorics and number theory constantly need small `Finset` lemmas that don't exist yet.

5. **Measure theory infrastructure** — Measure theory is used by probability, analysis, and ergodic theory. Improving the API here unblocks multiple downstream areas.

6. **Help with Lean 4 toolchain bumps** — When Lean releases a new version, Mathlib needs to adapt. This is always urgent and always needs help.

---

## The Meta-Lesson

The most valuable contributors to large open-source math formalization projects are not necessarily the ones who formalize the most impressive theorems. They are the ones who:

- **Make other contributors more productive** (reviews, tooling, documentation)
- **Keep the project healthy** (CI, refactoring, deprecation cleanup)
- **Reduce friction** (better error messages, better APIs, better onboarding)

If you can do 2 hours of PR review per week consistently, you will likely have more impact than someone who spends 20 hours formalizing a niche theorem. The compounding effect of unblocking others is enormous.

---

## Resources

- [Mathlib Contributing Guide](https://leanprover-community.github.io/contribute/)
- [Mathlib Style Guide](https://leanprover-community.github.io/contribute/style.html)
- [Lean Zulip](https://leanprover.zulipchat.com/)
- [Mathlib4 GitHub](https://github.com/leanprover-community/mathlib4)
- [Lean4 GitHub](https://github.com/leanprover/lean4)
- [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html)
