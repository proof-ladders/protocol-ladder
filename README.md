[TOC]

# Intro

This repository aims to accumulate a set of examples, for the formal analysis of crypto primitives and protocols.

All difficult levels are subjective: easy, medium, hard, extreme, with an additional Out-Of-Scope (OOS)(impossible to model for some reasons).

TODO: give an intuition/criterion of what each difficulty levels should reflect?

Question marks indicate that a proof file remains to be completed for the corresponding case.

All completed files can be found in corresponding subdirectories.

Tools:
 * ProVerif: `.pv` files
 * Tamarin: `.spthy` files
 * DY*: ?
 * Squirrel: `.sp` files
 * Cryptoverif: `.ocv` files
 * EasyCrypt: `.ec` files


TODO: For each tool, an indicative difficulty ranking between the multiple case studies could be proposed?


# Primitives



Current primitive examples:
* Encrypt-Then-Mac is IND-CPA + INT-CTXT

Possible ideas:
* IND-CPA KEM from DH + ROM 
* play around DDH/CDH/gapDH
* biKEM from dualPRF + two IND-CPA KEM

All primitives are OOS for symbolic tools.

All primitives models in Squirrel will have a weaker attacker model (only asymptotic security, limitation being lifted in WIP)

## Encrypt-Then-Mac is IND-CPA + INT-CTXT

subolder: [EtM-IND-CPA+CTXT](EtM-IND-CPA+CTXT/)

| Squirrel | CryptoVerif | EasyCrypt |
| --------:| ----------- |:--------- |
|  Medium? | Easy        | Easy?     |



# Protocols

Current protocols:
* signed Diffe-Hellam (auth+secrecy)
* NTOR (auth+secrecy)
* basic-hash (auth+unlinkability)


Possible ideas:
* PQXDH? (highlight PQ sound capabilities, existing model in ProVerif and CryptoVerif, but quite similar to NTOR, so probably redundant)
* a signed hybrid KEM instead?


## Signed Diffie-Hellman

subolder: [signedDH](signedDH/)

| Proverif | Tamarin | DY* | Squirrel | CryptoVerif | EasyCrypt |
| -------- | -------:| --- | -------- | ----------- | --------- |
| Easy     |    Easy | ?   | Easy  | Easy        | HARD      |

Possible extensions: LTK compromise (for Forward Secrecy) + Ephemeral compromise.

* LTK compromise: does not really increase difficulty
* Ephemeral compromise: OOS for CryptoVerif.


TODO: harmonize files

## NTOR protocol

subolder: [ntor](ntor/)

spec: https://spec.torproject.org/proposals/216-ntor-handshake.html


| Proverif | Tamarin | DY* | Squirrel | CryptoVerif | EasyCrypt |
| -------- | -------:| --- | -------- | ----------- | --------- |
| Easy     |    Easy | ?   | Medium?  | Easy        | HARD      |


Possible extensions: LTK compromise (for Forward Secrecy) + Ephemeral compromise.

* LTK compromise: does not really increase difficulty
* Ephemeral compromise: OOS for CryptoVerif.

Notes:
* shows that ntor is "harder" than signedDH, due to authentication through static DH keys, which implies authentication based on gDH+ROM.

## Basic Hash

subolder: [basic-hash](basic-hash/)


| Proverif  |   Tamarin | DY* | Squirrel | CryptoVerif | EasyCrypt |
| --------- | ---------:| --- |:-------- | ----------- | --------- |
| HARD/OOS? | HARD/OOS? | ?   | Easy     | Medium      | Medium    |

Possible extensions:
 * several flavours of such protocols exists that have internal states, to store a counter or a timestamp. Only Squirrel manages this.

Notes:
* the privacy based unlinkability property makes it hard to manage for symbolic tools (dedicated tools like DeepSec are often needed in such a case).

