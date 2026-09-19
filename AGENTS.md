# Repository guidelines

## Markdown mathematics

- Use `$...$` for inline mathematics and `$$...$$` for display mathematics in Markdown documents.
- Put the opening and closing `$$` on separate lines, with blank lines separating the display from surrounding paragraphs.
- Do not use `\(...\)` or `\[...\]` as math delimiters, or backticks to display mathematical formulas as code.
- Use inline code or code blocks for Lean code, declaration names, file paths, commands, and syntax examples. Use the math delimiters above for mathematical variables, conditions, and expressions.

## External results and proof requirements

- [src/External/](src/External/README.md) is reserved for original theorems or formulas from external literature. Only Lean files in this directory may use `sorry`, and only for original results that have not yet been formalized. Lean code elsewhere must not use `sorry`.
- External statements must preserve the source's generality, parameters, hypotheses, and normalization conventions. Conversion lemmas adapting them to this project must be proved in full: reusable conversions belong in `src/General/`, and theorem-specific conversions belong in the corresponding theorem directory.
- Maintain a table in [src/External/README.md](src/External/README.md) mapping each file to its original source, theorem or formula number, and Lean declaration. Use a separate row for each result when a file cites multiple results. If the source has no number, give a section, page, or nearby numbered formula that locates it; do not invent a number.
- When adding, moving, changing, or deleting external results, update the registry, relevant imports, and audits together. Lean comments for external results must identify the original source.
- Do not bypass these rules with `admit`, direct calls to `sorryAx`, or new project `axiom` declarations. Other directories may depend on registered external results, but must prove their own conversions and proof steps.
- After reorganizing or changing Lean code, run `lake build` and confirm that compilation and existing audits pass before committing or pushing.

## Lean naming

- Give Lean files, namespaces, and declarations stable names describing the mathematical object, conclusion, or hypotheses. Do not name them after theorem, lemma, proposition, or formula numbers in the manuscript.
- Renumbering the manuscript must not require renaming Lean interfaces. Do not retain aliases for old number-based names. Record manuscript correspondences in comments or the relevant directory README, preferably using stable LaTeX labels.
- Register original theorem and formula numbers from external literature as required above, and include them in source comments and the External table. Those numbers are not declaration names.
