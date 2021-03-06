# Assignment 1: Scheme Reader

In this assignment you'll implement the first stage of your Scheme compiler, the Reader. The main task is to complete 
the code in `reader.ml`.

## Requirements

Read the PDF file included in this repository to get the reader specifications and other requirements.

## Git

You'll be implmeneting this (and future) assignments by adding code to a Git repository. The first thing you need to 
do is download and install a copy of [Git](https://git-scm.com/downloads).

To get a local copy of your git repository, you need to enter the command `git clone <repository_url>`. Afterwards, the 
general Git workflow for your work is: 
- `<implement parts of the assignment>`
- `git add <modified_file_1> <modified_file_2>` or, to include all changed files `git add *` 
- `git commit -m "<short description of what you did>"`
- `git push`

Any part in angle-brackets should be filled out by your specific input

### git clone

The `git clone` command copies a repository from a remote URL down to your computer and links your local copy with that 
remote repository so you can upload code back into that remote repository.

A reference where you can find your repository URL:
![git clone URL](/readme.d/git_clone.png?raw=true)

###  git add
The `git add` command tells Git to track the files you selected (or all files in the current directory, recursively if 
you used `*`). Tracking means these files will be included in the next commit

To see what files are "added", you can use the  `git status` command and look under "Changes to be committed". Only 
files listed there will be included if you run `git commit` (see below)

### git commit
The `git commit` command tells Git to collect all tracked files (see [git add](#git-add)) into a single "transaction" 
called a "commit" and attach a message to that commit (using the `-m` parameter).

Commits are the basic unit of work in Git.

### git push
The `git push` command takes all the commits you created locally, and sends them to the remote repository (by default, 
the URL from which you cloned the repository). This command actually uploads your work to the server, at which point 
you can see the changes on GitHub.

## VM

Since we'll be grading your work on a Linux machine, and since we wanted you all to use the same software versions as we 
do for grading, we provide you with a VM. However, since setting up the VM for efficient use might take some effort, 
and can be frustrating we'll be using two industry standard tools to run this VM - VirtualBox and Vagrant. You've used 
VirtualBox before, so we'll skip that bit.

### Vagrant

This repository contains a Vagrant setup file called `Vagrantfile` (paraphrasing on `makefile`). Vagrant is a tool for 
sharing VMs. It includes the VM image, setup, configuration, network connections and just about anything you'd want to 
configure before you start working. The vagrantfile contains all the commands required to setup your VM.

#### Using Vagrant
First, download and install [Vagrant](https://www.vagrantup.com/downloads) for your OS. Next, open a terminal in the 
project's root directory (where this `README.md` file is stored) and run `vagrant up`. When running this command
for the first time it might seem like it's stuck on "Downloading" for up to 3 hours, depending on your internet
connection. It's not stuck. 

Note: On windows, Vagrant doesn't give you any indication of download progress, so you can take a look in 
`%HOMEPATH%/. vagrant.d/tmp` and see the file there that represents the downloading VM. Once it reaches 7GB, Vagrant
will continue setting up your VM

The `vagrant up` command will read the Vagrantfile, download the correct VM image, create the VM using VirtualBox, 
create a shared folder between the VM and the host, setup an SSH connection between the VM and start the VM. The first
time you run `vagrant up` the VM image it downloads is rather large (7GB). If you run `vagrant up` again (e.g. if to 
rebuild your VM), Vagrant will use a local cache of the VM image, so it will run MUCH faster (less than a minute).

To connect to your VM, you need to run `vagrant ssh`. This will open an SSH connection to your VM and provide you a 
shell in which you can run your code. Note, the project's folder is mapped to `~/compiler` in the VM (when you log 
in with `vagrant SSH` it will take you to the home folder at `~`), so the first command you execute should be 
`cd compiler`.

If you want to stop your VM, you can execute `vagrant halt`. It will gracefully terminate the VM.

When you want to delete your VM you can execute `vagrant destroy` (helpful if you accidentally destroy you VM somehow). 
Note, if you don't want/can't use `vagrant destroy`, you need to delete the VM from VirtualBox **AND** delete the 
`.vagrant` folder inside the project's root with `rm -rf ./.vagrant` (executed from within the project's root).

### Connecting to the VM graphically
The VM created by `vagrant up` is a regular VM in VirtualBox, so if you'd like, you can just open up the VirtualBox
dashboard, and double-click the relevant VM. The password for the Vagrant user is `vagrant`. 

The VM comes with VScode, Intellij and Emacs all three with their Ocaml plugins. Also it comes preinstalled with Scheme, 
Ocaml, utop, gcc, gdb, nasm and whatever tool we figured you might need to work on this and future assignments. Of course
You can always install any other tool you like from the Ubuntu repositories with `apt install`

## Testing your assignment 

To help imrpove your chances at a good grade, we HEIGHLY recommend you use a form of unit testing. However, we often see 
cases of students who write their testing code inside their assignment (i.e. inside `reader.ml`), which often leads to 
failures during grading because of leftover testing code.

The correct way to unit test your work is to create a separate testing file that loads your code (i.e. `reader.ml`) and 
applies tests to it. To encourage you to test your code correctly and quickly we're including the testing framework that 
will be used in grading your work (under the `tests` directory).

The way this testing framework works is by taking all the files in `tests/cases`, running them through your reader, 
converting the results back into s-expressions and using Scheme's `equal?` function to compare the original input with 
your output.

To run these tests you simply open a terminal in your project's root dir and run `tests/test_cases.sh` and you should 
see the result for each tested file. So for a frash repo you should see:
```
$ cat tests/cases/boolean.scm
#t #f

$ tests/test_cases.sh 
--------------------boolean.scm--------------------:
Exception: X_not_yet_implemented.
FAIL: 
```

And after yout first implemente Booleans incorrectly (for the sake of demonstration) you might see something like:
```
$ tests/test_cases.sh 
--------------------boolean.scm--------------------:
FAIL: `(tests/cases/boolean.scm: ,(equal? '(#t #f) '(#t #\f)))
```

And finally, after implementing some parsers (correctly) and adding a test of your own called `my_test.ml` to 
`tests/cases`, you will see:
```
# cat tests/cases/my_test.scm
#t #\t 1 abc

$ tests/test_cases.sh 
--------------------boolean.scm--------------------:
PASS: (tests/cases/my_test.scm: #t)
--------------------my_test.scm--------------------:
PASS: (tests/cases/my_test.scm: #t)
```

Again, **we heighly encourage you to add your tests to the tests/cases/** so you can test your code quickly and often.

### Bug bounty
Since we will be using the above framework to test your code (or at least something etrememely similar) any bug that you 
find in this system might (and probably will) affect the grading process. In an attempt to resolve such issues before 
they cause any problems we're starting a [bug bounty program](https://en.wikipedia.org/wiki/Bug_bounty_program) for 
which any unique bug is worth 1 point on your final grade.

Conditions:
1. Bug must be usable to cause an incorect output to received a "PASS" output from the `test_cases.sh` script
1. Bug report must include example case and `reader.ml` implementation that should fail for the example case but passes 
the test by exploiting the bug 
1. Single bounty per student
1. Single bounty per bug (first report over email/Students requests system awards the bounty)
1. Bug must not depend on changes under the `tests` directory (which will be overriden during grading with our 
implementation and test cases)
1. Bug must be explitable in an unmodified VM image as provided by the course staff on the course's Moodle page.

## Submission
When you push your work to the remote repository, you update the "main" branch for the remote repository. The latest 
commit in your "main" branch at the time when the deadline expires will be your submitted work. 

To associate your work with your BGU user, you'll need to submit a single file to the submission system. You should
execute: `git remote get-url origin > submission`. This command will create a file called `submission` that conatins
the URL to your repository. You should upload that file, and nothing else, to the submission system.
