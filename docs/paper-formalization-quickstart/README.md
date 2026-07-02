# Paper Formalization Quickstart guide for humans

Give the agent an arXiv link or paper pdf/source, and also mention where the published version is for its records.

```text
Get context on this repo and skills and formalize
<paper link>.
```
Set a durable goal:
```text
/goal fully formalize <PaperFolder> until full done, and then run the post formalization audit.
```

I often queue up a bunch of
```text
keep going until closeout
```
commands in Codex, but this is increasingly not needed given a goal.

Useful steering advice:
- I often ask it for the status and steer it into proving one thing or another first.
- Often it will state something is a caveat/error in the paper, but I ask it to look for the source assumptions carefully and usually it'll find it.
