# Intro

This repository aims to accumulate a set of examples, for the formal analysis of cryptographic primitives and protocols.

## Protocols

This README is not standalone, the problem sets and possible modeling options are detailed in the [pdf notes](https://github.com/charlie-j/fm-crypto-lib/blob/main/Notes/main.pdf).

For each problem, this repository contain a corresponding subfolder. The corresponding problem folder contains for each tool that proposed a solution a corresponding subfolder with the name of the tool, subfolder that contains the corresponding modeling files for the solution. 

We encourage tool developers to in addition to the solution files to provide in a dedicated repository more detailed versions of the solutions, potentially with a full incremental tutorial, or partial solutions with corrections.
The corresponding repositories are listed as:
* Tamarin: https://github.com/auroranaska/hacs-tamarin-2025


We also expect that each solution comes with a quick standardized decription, following the template provided here: (see the pdf notes to better understand the terminology)
```
Model features:
 * attacker: active/passive    // whether the attacker is active or passive
 * sessions: n/∞ // whether there is a bounded (precise number n) or unbounded number (∞) of possible session
 * agents: n/∞ //  there is a bounded or unbounded number of agents
 * compromises: none/LTK/EK/EK+LTK
  // LTK means that there is only long term key compromise
  // EK means that there is only only ephemeral key compromise
  // EK+LTK enables both
 * Attacker class: computational/symbolic
 * Primitives: IND-CCA/UF-CMA/.../signature/signature with DEO/...
   // if approach is computational, this contains the list of assumptions
   // if it is symbolic, it contains the list of primitives with eventual advanced capabilities
 * Properties: Prop1, ..., ⚡Propi, ..., Propn
  // provide here the properties or class of attacks covered by the tool.
  // by default, giving a property means it is proved.
  // for tools that enable attack finding, a found attack on a property is given by prefixing the property with the  ⚡ emoji.
  

Analysis features:
  * difficulty ratings:	easy/medium/hard/possible/impossible (X), easy/medium/hard/possible/impossible (Y), ...
    // relative difficulty of the analysis (in case of WIP, this is of course an expected difficulty rating)
	// possible means that it is theoretically possible, but would require for the moment unreasonable effort
	// if relevant, several disting ratings may be given, for example X might be a set of easy properties to prove
	// and Y a set of hard properties
  * status: ✅/WIP/❎
    // status of the solution, if the model and proofs are fully complete (✅), do not exist at all (❎), or is partially completed (WIP)	
``` 

This standardized description can be extended at will be the authors, for instance in a dedicated README in the solution subfolder or in their own repository. We provide tables agregating those standardized description for each problem below.

As of now, only the Basic Hash problem provides the begining of what we hope to provide for all problems.

## Primitives

WIP



# Protocols

## Problem 1: Basic Hash

subolder: [basic-hash](basic-hash/)

| Tool        | Attacker | Sessions | Agents | Compromises | Attacker Class | Primitives | Properties | Difficulty ratings          | Status |
|:----------- | -------- | :--------: | :------: | ----------- | -------------- | ---------- | ---------- | --------------------------- | :------: |
| Squirrel    | Active   | ∞        | ∞      | None        | Computational  | PRF        | Auth, Unli | Easy                        | ✅     |
| CryptoVerif | Active   | ∞        | ∞      | None        | Computational  | PRF        | Auth, Unli | Easy                        | ✅     |
| EasyCrypt   | Active   | ∞        | ∞      | None        | Computational  | PRF        | Auth, Unli | Hard                        | ✅     |
| Tamarin     | Active   | ∞        | ∞      | None        | Symbolic       | Hash       | Auth, ⚡RA | Easy (Auth,RA), Hard (Unli) | WIP    |
| Proverif    | Active   | ∞        | ∞      | None        | Symbolic       | Hash       | Auth, ⚡RA | Easy (Auth,RA), Hard (Unlo) | WIP    |


## Signed Diffie-Hellman

WIP

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


WIP 

spec: https://spec.torproject.org/proposals/216-ntor-handshake.html


| Proverif | Tamarin | DY* | Squirrel | CryptoVerif | EasyCrypt |
| -------- | -------:| --- | -------- | ----------- | --------- |
| Easy     |    Easy | ?   | Medium?  | Easy        | HARD      |


Possible extensions: LTK compromise (for Forward Secrecy) + Ephemeral compromise.

* LTK compromise: does not really increase difficulty
* Ephemeral compromise: OOS for CryptoVerif.

Notes:
* shows that ntor is "harder" than signedDH, due to authentication through static DH keys, which implies authentication based on gDH+ROM.


## Showcase

| Tool      | Case-study | Description | Link |     |
| --------- | ---------- | ----------- | ---- | --- |
| EasyCrypt | Kyber      | WIP         | WIP  |     |
| Tamarin   | WIP        | WIP         | WIP  |     | 

# Primitives


Current primitive examples:
* Encrypt-Then-Mac is IND-CPA + INT-CTXT
* KEM+DEM is semantically secure as a PKE

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
|  Medium? | Easy        | Easy     |

## KEM+DEM is semantically secure as a PKE

subfolder: [kemdem](kemdem/)

| Squirrel | CryptoVerif | EasyCrypt |
| --------:| ----------- |:--------- |
|  Medium? | Easy        | Easy     |

# Acknowledgments

This initiative was pushed forward by the HACS workshop. The main contributors for the design of the problems set are: Manuel Barbosa (primitives), Cas Cremers (protocols), François Dupressoir (primitives and protocols), Charlie Jacommme (protocols), Aurora Naska (protocols), Trevor Perrin (main coordinator), Mike Rosulek (primitives). We additionally thanks the following for their valuable feedback: Karthikean Barghavan, Jonathan Katz, Devon Tuma, Bas Spitters,Théophile Wallez. We expect that each solution and tool repository comes with additional authoring mentions.


