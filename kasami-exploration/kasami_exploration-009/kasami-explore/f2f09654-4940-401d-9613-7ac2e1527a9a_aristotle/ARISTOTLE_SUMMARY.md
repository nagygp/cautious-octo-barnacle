# Summary of changes for run f2f09654-4940-401d-9613-7ac2e1527a9a
I've written a comprehensive guide at `CONTRIBUTING_GUIDE.md` covering your questions in detail. Here are the key takeaways:

**Highest-leverage (80/20) contributions:**
1. **PR review** — the single highest-leverage activity. Mathlib is chronically bottlenecked on reviewers, not authors. One good reviewer unblocks dozens of contributors.
2. **CI/build maintenance** — keeping `master` green, adapting to Lean toolchain bumps.
3. **Import graph optimization** — reducing compile times, which affects every single contributor.
4. **`simp` lemma hygiene** — auditing `@[simp]` tags; bad ones slow the entire library.

**Your intuition is correct:** Maintenance and refactoring are generally more valuable than new theory. New theory PRs are abundant (many mathematicians want to formalize results); maintenance PRs are scarce (few people enjoy it). The bottleneck is almost never "not enough new content."

**Areas with fewest maintainers / most help needed:**
- **Mathlib:** Combinatorics, analytic number theory, probability theory, category theory maintenance, tactic maintenance (many tactics have a single author-maintainer)
- **Lean 4 Core:** Lake (build system), error messages/diagnostics, editor integration

**High-leverage maintenance tasks:**
- Deprecation cleanup, API gap filling (especially `Finset`/`List`/`Order`), performance profiling, linter improvements, universe polymorphism fixes

**Best practices:**
- Start with small PRs, join Zulip first, claim `good first issue` items, don't work in isolation on large projects
- Focus on making other contributors more productive — that compounds far more than individual theorem formalization

The full guide includes a detailed impact/barrier-to-entry table, concrete project suggestions, PR and review best practices, and links to key resources.