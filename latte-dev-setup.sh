#! /bin/env bash

echo "LaTTe development setup script"
echo "=============================="

DEVREPO="origin"
DEVBRANCH="master"

if [ -n "$1" ] && [ -n "$2" ]
then
    DEVREPO="$1"
    DEVBRANCH="$2"
elif [ -n "$1" ]
then
    DEVBRANCH="$1"
fi

echo "Repository = $DEVREPO"
echo "Branch = $DEVBRANCH"

echo "\nLaTTe kernel"
echo "------------"

if [ -e "../latte-kernel" ]
then
    echo " ==> Updating repository"
    (cd "../latte-kernel" ;
    git pull "$DEVREPO" "$DEVBRANCH" ;
    echo " ==> Installing kernel"
    lein install)
else
    echo "Kernel not found, skipping"
fi

echo "\nLaTTe (main)"
echo "-------------"

echo " ==> Updating repository"
git pull "$DEVREPO" "$DEVBRANCH"
echo " ==> Installing LaTTe"
lein install

echo "\nLaTTe prelude"
echo "--------------"

if [ -e "../latte-prelude" ]
then
    echo " ==> Updating repository"
    (cd "../latte-prelude" ;
    git pull "$DEVREPO" "$DEVBRANCH" ;
    echo " ==> Certifying prelude"
    lein certify ;
    echo " ==> Installing prelude"
    lein install)
else
    echo "Prelude not found, skipping"
fi

echo "\nLaTTe sets"
echo "------------"

if [ -e "../latte-sets" ]
then
    echo " ==> Updating repository"
    (cd "../latte-sets" ;
    git pull "$DEVREPO" "$DEVBRANCH" ;
    echo " ==> Certifying library"
    lein certify ;
    echo " ==> Installing library"
    lein install)
else
    echo "Latte-sets not found, skipping"
fi


echo "==========================="
echo "\n LaTTe ready for hacking!"

