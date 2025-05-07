# Verified primality testing

**Contributors**: Siddhartha Gadgil, Bhavik Mehta, Anand Rao Tadipatri

## Lucas Primality testing

The [Lucas primality test](https://en.wikipedia.org/wiki/Lucas_primality_test) is a converse to Fermat's Little theorem which states that if a number $n > 2$ has the properties that
- there is an integer $a$ strictly between $1$ and $n$ such that $a^{n-1} \equiv 1 \pmod{n}$ 
- for every prime factor $q$ of $n-1$, $a^{(n-1)/q} \not\equiv 1 \pmod{n}$
then $n$ is prime.

## Pratt Certificates

The [Pratt certificate](https://en.wikipedia.org/wiki/Pratt_certificate) is based on the idea that given a candidate integer $a$ and a factorisation of $n-1$, it is easy to verify the conditions for the Lucas primality test. The certificate will have to be recursive in nature, since proving primality of $n$ by the Lucas test requires proving primality of the individual factors of $n-1$.

This code uses the computer algebra system [PARI/GP](https://pari.math.u-bordeaux.fr/) to generate these pieces of data, which are then formally verified within Lean (see `MetaComputeTest/Pari.lean`).

## Efficient modular exponentiation

The test involves performing several calculations of the form $a ^ b \pmod{m}$, which can be optimised by [iterated squaring](https://en.wikipedia.org/wiki/Exponentiation_by_squaring) and reducing modulo $n$ at each step. 

Normalising an expression like $a ^ b \pmod{m}$ via kernel reduction is slow, since it does the calculation the direct way. Instead, we write a meta-program to enforce a custom evaluation strategy (see `MetaComputeTest/PowerMod.lean`).

## Tactic

The entire pipeline of generating certificates using PARI/GP and verifying them in Lean is done using the `pratt` tactic, which gives a code action suggestion to replace itself with a tactic block containing the certificate (see `MetaComputeTest/Pratt.lean`).