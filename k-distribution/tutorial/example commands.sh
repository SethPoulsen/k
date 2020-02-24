which kompile
cd tutorial/1_k/1_lambda/lesson_1
ls
kompile --backend llvm lambda.k
ls
time kompile --backend llvm lambda.k
ls
cat README.md 
krun identity.lambda
kast identity.lambda
ls
ls lambda-kompiled/
ls lambda-kompiled/interpreter 
ls
ls tests/
krun tests/identity.lambda
kast tests/identity.lambda
