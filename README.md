# Brown CS 1951x: Formal Proof and Verification, 2023

In this repository, you'll find Lean files for [CS1951x](https://browncs1951x.github.io/).

## Using this repository

This repository is a [Lean project](https://leanprover-community.github.io/install/project.html).
There are some basic steps you should take at the beginning to set it up.
These only need to be done once.
If and when you need to create any new `.lean` files,
create them in the `src` directory of this project,
to ensure that all your expected imports are available.

### Setup

We assume that you have installed:
* `git`
* `lean` (via `elan`)
* VSCode and the Lean extension

following our [course setup instructions](https://browncs1951x.github.io/setup.html).

    
To set up this project, run:

```bash
git clone https://github.com/BrownCS1951x/fpv2023.git
cd fpv2023
lake exe cache get 
lake build LoVe.LoVelib
```

When you open VSCode, make sure that you use the **Open Folder** feature
to open the entire `fpv2023` directory,
instead of opening individual files. 
The easiest way to do this is from the command line:
```bash
cd fpv2023
code .
```
But `File -> Open Folder...` works fine too.

### Pulling changes

We will add files to this repository as the course progresses,
and occasionally edit old files. 
We will try very hard to make the homework assignments "read-only":
once they are posted, we will not modify them, and will announce if we do.

You can check whether you have modified any files in the repository with
```bash
git status
```
If you have no modified files, pulling our updates is easy:
```bash
git pull
```
If you have modifications, you should either commit them:
```bash
git commit -am "your message here"
git pull
```
or stash them:
```bash
git stash
git pull
git stash pop
```

Note that modifying files could potentially lead to merge conflicts.
For this reason, especially with the homeworks,
we recommend editing a copy of the files:
```
cp src/homework/homework_1.lean src/homework/homework_1_rob.lean
```

I would complete the homework in the copy, `homework_1_rob.lean`, 
and submit that file on Gradescope.

### Debugging

The Lean files should be quick to load. 
If you see orange bars in VSCode for a long time (20 seconds is way too much),
something might be wrong.
This can be caused by accidentally making changes to library files,
or by having too many files open in VSCode that import each other.

First, in VSCode, close any editor tabs that you aren't using anymore.
Then open the Command Palette (`ctrl-shift-p` or `cmd-shift-p`)
and run `Lean 4: Restart Server`. 

If that doesn't work, let's make sure you have a fresh copy of the library.
In the root `fpv2023` directory, run:
```bash
lake update
lake exe cache get 
lake build LoVe.LoVelib
```
If this last line takes more than a few seconds, things might still be wrong.
Talk to Rob or the TAs.

## Contents

`src/lovelib.lean` is a mini-library that we will use for this class.

### Lecture notes

We are following the text *The Hitchhiker's Guide to Logical Verification*.
Corresponding to each chapter of the text, there is a `.lean` file that we will work through in class.
These files are posted here in the `Lectures` folder.

### Exercises

The files in the `Exercises` folder are "homework-like" problems for extra practice.
There will be an optional weekly lab session to work on these exercises.
The labs aren't required, but are great practice for the homeworks,
a good opportunity to make up the difference between the theory in lectures and the practice on assignments.
These lab sessions will be collaborative.
Solutions to the exercises will be posted.

### Homework assignments

There is approximately one homework assignment per chapter of the Hitchhiker's Guide.
These will be posted on or before the day of the corresponding lecture, 
and will be due after the following week's lecture.
You may discuss problems with your classmates, but the work you submit must be your own.
We recommend the "clean blackboard" method: 
after discussing the problem, erase your blackboard/editor window/etc, 
and write up the solutions individually.
Homeworks will be posted in the `Homework` folder.
