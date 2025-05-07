import MetaCompute.Pari

open pari

/-- info: "1" -/
#guard_msgs in
#eval queryPari "isprime(85083351022467190124442353598696803287939269665617)"

/-- info: "[2 3]\n\n[3 1]\n\n[5 1]" -/
#guard_msgs in
#eval queryPari "factor(120)"


/-- info: "Mod(5, 85083351022467190124442353598696803287939269665617)" -/
#guard_msgs in
#eval queryPari "znprimroot(85083351022467190124442353598696803287939269665617)"

/-- info: false -/
#guard_msgs in
#eval isPrime 120
/-- info: [(2, 3), (3, 1), (5, 1)] -/
#guard_msgs in
#eval factors 120

/-- info: 5 -/
#guard_msgs in
#eval znPrimRoot 85083351022467190124442353598696803287939269665617 -- 5
