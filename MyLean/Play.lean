
#eval 1 + 2 * 5

#eval String.append "Hello, " "Lean!"

#eval String.append "it is " (if 1 > 2 then "yes" else "no")

def add1 (n : Nat) : Nat := n + 1

#eval add1 7

#check add1
