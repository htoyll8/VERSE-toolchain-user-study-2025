# Contributing guidelines

Learn how the VERSE team develops the toolchain and how you can contribute.

## Start here

Before you dive in, [set up your development environment](#setting-up-your-development-environment) to automatically enforce
our style guidelines and linting rules. These avoid needless nitpicking in code
reviews.

We use [this GitHub project](https://github.com/orgs/GaloisInc/projects/23) to
track and coordinate development.

- All work starts by creating an issue.
- The issue is done when the work is done, tested, reviewed, and merged.

Read [contributing code](#contributing-code) for a step-by-step guide and an
explanation of why we do things this way.

Finally, read through these best practices guidelines.

- [VERSE-specific guidelines](#verse-specific-guidelines)
- [Coding principles](#coding-principles)
- [Git guidelines](#git-guidelines)
- (external) [A wonderful, general overview of best practices](https://gitlab-ext.galois.com/program-analysis/guidance/-/blob/master/BestPractices.org) ([permalink](https://gitlab-ext.galois.com/program-analysis/guidance/-/blob/78d2d6229f027579384c39a76cf28026b03279a7/BestPractices.org))

Wondering if the squeeze is worth the juice? Jump to [Why this process?](#why-this-process)

## Setting up your development environment

To do: link to code format and lint configurations for each language we use.

## Contributing code

We are following [Trunk Based Development](https://trunkbaseddevelopment.com/)
methodology. Here's the development workflow.

1. [Create an issue](#create-an-issue)
1. [Create a branch](#create-a-branch)
1. [Write your code](#write-your-code)
1. [Create a PR and get it reviewed](#create-a-pr-and-get-it-reviewed)
1. [Merge your PR](#merge-your-pr)
1. [Delete your branch](#delete-your-branch)

### Create an issue

Create a GitHub issue describing the change you're planning to make.

- Assign it to yourself.
- Add a label for your organization (Galois, UCam, etc.)
- Add labels for the type of work (IDE, CN, documentation, etc.)

Creating an issue automatically adds it to the project board, which helps us
track and prioritize ongoing work across different teams and organizations.
Tying issues to development work (and PRs) also makes it easier to answer questions
in the future, like "What went into the release we sent to the user study last
year?" or "What exactly did we fix from the red team's report?"

### Create a branch

Create a topic branch named `XX-issue-name` where XX is the issue number.

Naming branches this way makes it clear which branch corresponds to which issue
and makes it easier to keep the repo clear of unused or outdated branches. An
easy way to create a branch following this convention is to click the _"create a
branch"_ button on the issue page and then check out the newly created branch
locally.

### Write your code

Here are some things to consider as you develop on your branch:

- Write unit and integration tests.

- Merge regularly from the main branch.

- Rebasing from the main branch (`git pull --rebase origin main`) is not recommended. See [the "Merging" section in these guidelines](https://gitlab-ext.galois.com/program-analysis/guidance/-/blob/master/BestPractices.org?ref_type=heads#:~:text=updating%20a%20submodule.-,Versioning,-Versioning%20should%20follow) for the reasoning.

- Push regularly to your remote branch. This saves your work and runs CI tests.

When you're done...

### Create a PR and get it reviewed

When you are ready to have your changes reviewed, create a PR on GitHub.

- Summarize your change.
- Tag one or more reviewers.
- Link to the issue it addresses using `closes/resolves/fixes #XX`, where XX is the issue number.

At least one reviewer needs to approve your PR. The _reviewer_ should either:

- **Request changes** for blocking/breaking issues and tricky fixes that require re-reviewing.
- **Approve** for suggestions/opinions that you trust the code author to consider and address as they see fit. Approving without comments or a simple _LGTM_ is acceptable.
- **Comment** for giving early feedback on a longer review.

For example, a reviewer marks a PR as _Approved_ even though they added a couple
of commments about the PR – the author can address (or ignore) them as they see
fit, and then merge without another round of reviewing.

Consider reflecting significant change requests or discussion points back into
the related issue(s) as appropriate.

### Merge your PR

Ideally, your commit history will reflect small, targeted, well-formed commits
that play nicely with `git bisect`. If not, consider using "squash and merge".

### Delete your branch

GitHub usually does this for you. Consider updating your local state with

```
git checkout main
git pull
git branch -d your-branch-name
```

Git will warn you if you try to delete a branch that hasn't been merged.

## VERSE-specific guidelines

- Use language-appropriate naming conventions for naming files and folders, and default to _snake_case_ when in doubt. The only exceptions are:
  - the top-level files, such as `README.md`, `CONTRIBUTING` and such.
  - `Dockerfile*` is capitalized, per Docker [naming conventions](https://stackoverflow.com/a/63995752)
  - `Makefile*` is capitalized, per GNU Make [naming conventions](https://www.gnu.org/software/make/manual/make.html#Makefile-Names)
- Include [submodules](https://git-scm.com/book/en/v2/Git-Tools-Submodules) at the point of use (e.g. `./foo/bar/my_submodule`), rather than in the root directory (`./my_submodule`).

## Coding principles

- Explicit is better than implicit
- Code should be written to be read, and not to make writing more convenient; assume that the person reading the code is you in a year
- Comments are critical, and should prioritize explaining why rather than what
- Similarly, good commit messages are required; good commit messages explain why a change was made (including links to issues where appropriate or reference to observed incorrect behaviors that may inform others who see similar failures) (more on this in [Git guidelines](#git-guidelines))
- Strive to make error states unrepresentable (but not at the expense of clarity)
- Advanced development tools are great, but should not be required to develop a project
- Libraries should not call exit or produce console output (unless initiating a truly mandatory crash); libraries should not have fatal crashes
- Prefer library-first development (the functionality of any program should be available as a library)
- A clean version control history is important (e.g., to support bisecting and code understanding), but extensive history rewriting is not important (more on this in [Git guidelines](#git-guidelines))

## Git guidelines

- Do not commit directly to `main`.
- To support bisecting, do not merge WIP commits that break the build.
  On topic branches, squash commits as needed before merging, but only
  to reduce excessive small commits; the development history of topic
  branches should be preserved as much as is reasonable. Use your
  best judgement. Ask a git expert for advise if you are stuck more
  than 10 minutes.
- Write short, useful commit messages with a consistent style. Follow
  these [seven rules][], with the amendment that on this project, we
  have adopted the convention of ending the subject line with a
  period. Galois has excellent resources about commit messages, please consult
  [What goes into a commit](https://confluence.galois.com/pages/viewpage.action?pageId=82346420)
- Keep your topic branches small to facilitate review.
- Before merging someone else's PR, make sure other reviewers'
  comments are resolved, and that the MP author considers the PR ready
  to merge.
- For security-sensitive code, ensure your changes have received an
  in-depth review, preferably from multiple reviewers. Please consult [Code reviews page](https://confluence.galois.com/display/EN/Code+Reviews) for more details.
- Configure Git so that your commits are [signed][].

- Avoid `git push --force`. If you must, make sure that you know that no one else has pushed changes to the branch that are not in the history of your local branch. If others on the team are pulling and testing it locally, they will need to fix up their local branches with `git checkout <yourbranch>`, `git fetch`, and `git reset --hard origin/<yourbranch>`. For more details, please see [The Dark Side of the Force Push][] and [--force considered harmful; understanding git's --force-with-lease][].

[The Dark Side of the Force Push]: http://willi.am/blog/2014/08/12/the-dark-side-of-the-force-push/
[--force considered harmful; understanding git's --force-with-lease]: https://developer.atlassian.com/blog/2015/04/force-with-lease/
[seven rules]: https://chris.beams.io/posts/git-commit/#seven-rules
[signed]: https://git-scm.com/book/en/v2/Git-Tools-Signing-Your-Work

## Why this process?

We are coordinating development across a variety of teams at different organizations around the world, and the project is expected to run for several years. Despite the long duration, our timeline is tight. Hence, we need to balance several concerns:

- **Visibility**. We need to understand what work has been planned, started, completed, or blocked, and who is doing it, in order to prioritize our next steps as things slip or circumstances change. We use issues and the project board for this.

- **Accountability**. When code changes, we need to understand why. This sometimes lives in commit messages, PR messages, issues, or a developer's head. In this project, we're standardizing on issues, which is why all work starts with an issue.

  - Commit messages should still be informative support `git log` and `git bisect`.

- **Development best practices.** Software engineering research and personal experience both suggest that coherent contribution guidelines ease development while raising the level of assurance. See [here](https://gitlab-ext.galois.com/program-analysis/guidance/-/blob/78d2d6229f027579384c39a76cf28026b03279a7/BestPractices.org) for motivation and details of specific best practices, some of which are adopted in this document.

- **Developer ergonomics**. Development should focus on building neat stuff, not fighting a process. We don't want to add boilerplate for no reason.
