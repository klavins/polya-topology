# Polya Topology

A Polya content repository: one Lake project whose Lean files carry the subjects, their
mathematics written for the student in the comments and the reference solutions as the
declarations. `about.yaml` names the repository; each subject's root module carries its
`@subject` block; each section file its `@section`, concepts, and problems.

```bash
polya new "A Subject"      # a subject with its first section
polya build asubject       # does the Lean compile?
polya extract asubject     # every problem checked against its spec
polya publish asubject     # to the instance in .env (POLYA_SERVER, POLYA_API_KEY)
```

## Authoring with Claude Code

The `polya-author` skill teaches Claude Code this kind of project: the annotated Lean, the
directory layout, the textbook voice, and what publishing checks. It lives in MUPolya:
https://github.com/klavins/MUPolya/tree/main/skills/polya-author

To install it for yourself, once:

```bash
git clone https://github.com/klavins/MUPolya ~/Code/MUPolya    # if you do not have it
mkdir -p ~/.claude/skills
ln -s ~/Code/MUPolya/skills/polya-author ~/.claude/skills/polya-author
```

or into this project alone, under `.claude/skills/polya-author`. Claude Code loads it when you
work on this repository's content.
