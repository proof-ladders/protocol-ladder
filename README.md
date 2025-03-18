# Intro

This repository brings together a set of examples for the formal analysis of cryptographic primitives and protocols. Our goal is to provide here a set of cryptographic problems, presented in pdf notes in a way accessible to both cryptographers or formal methods people, as well as a set of solutions for those problems, using distinct tools from the computer-aided cryptography domain.

If:
 * you are a *formal method curious cryptographer*, you should be able to understand all the problems, and then use the multiple solutions to discover the mutltiple tools, what kind of guarantees we can obtain with them, see which tools is best suited for which kind of analysis, ...;
 * if you are *cryptography curious formal verification researcher*,  you should be able to get a feel for the kind of guarantees cryptographers expects, and the variety of techniques that are currently used to get them;
 * if you are a *tool developper*, you can use this opportunity to showcase your tool and understand how it compares with others, on a set of clearly defined examkples.

We consider three separates set of problems, focusing on 
 * symmetric primitives;
 * asymmetric primitves;
 * protocols.

The following sections provide the details for each of those sets.


# Protocols

The problem sets and possible modeling options are detailed in the [pdf notes](https://github.com/charlie-j/fm-crypto-lib/blob/main/Notes/main.pdf), which should be read first. Then it is possible to explore the solutions, summarized below. For people hoping to get familiar with cryptographic definitions and proofs of key-exchanges, a pen-and-paper solution is available [here](https://github.com/charlie-j/fm-crypto-lib/blob/main/Notes/computational/main.pdf) for problem 2 (the signed DH protocol) and 4 (the simplified NTOR).

The directory structure for problems is as follows: there are top-level directories for each problem. Within these problem directories, there are tool-named subdirectories that contain solutions for that problem with the named tool.

We encourage tool developers to -- in addition to the solution files -- provide additional repositories with more detailed versions of the solutions, partial solutions with corrections, or additional incremental tutorials and materials.
The corresponding repositories are listed as:
* Tamarin: https://github.com/tamarin-prover/teaching

---
> [!IMPORTANT]
> We also expect that each solution comes with a quick standardized description, following the template provided here (see the pdf notes to better understand the terminology):
>```
> Model features:
>  * attacker: active/passive    // whether the attacker is active or passive
>  * sessions: n/∞ // whether there is a bounded (precise number n) or unbounded number (∞) of possible session
>  * agents: n/∞ //  there is a bounded or unbounded number of agents
>  * compromises: none/LTK/EK/EK+LTK
>   // LTK means that there is only long term key compromise
>   // EK means that there is only only ephemeral key compromise
>   // EK+LTK enables both
>  * Attacker class: computational/symbolic
>  * Primitives: IND-CCA/UF-CMA/.../signature/signature with DEO/...
>    // if approach is computational, this contains the list of assumptions
>    // if it is symbolic, it contains the list of primitives with eventual advanced capabilities
>  * Properties: Prop1, ..., ⚡Propi, ..., Propn
>   // provide here the properties or class of attacks covered by the tool.
>   // by default, giving a property means it is proved.
>   // for tools that enable attack finding, a found attack on a property is given by prefixing the property with the  ⚡ emoji.
>   
> 
> Analysis features:
>   * difficulty ratings:	easy/medium/hard/possible/impossible (X), easy/medium/hard/possible/impossible (Y), ...
>     // relative difficulty of the analysis (in case of WIP, this is of course an expected difficulty rating)
> 	// possible means that it is theoretically possible, but would require for the moment unreasonable effort
> 	// if relevant, several distinct ratings may be given, for example X might be a set of easy properties to prove
> 	// and Y a set of hard properties
>   * status: ✅/WIP/❎
>     // status of the solution, if the model and proofs are fully complete (✅), do not exist at all (❎), or is partially completed (WIP)	
> ``` 
>
>This standardized description can be extended at will by the authors, for instance in a dedicated README in the solution subfolder or in their own repository. We provide tables aggregating those standardized description for each problem below.
>

## Problem 1: Basic Hash

subfolder: [basic-hash](basic-hash/)

| Tool        | Attacker | Sessions | Agents | Compromises | Attacker Class | Primitives | Properties | Difficulty ratings          | Status |
| :---------- | -------- | :------: | :----: | ----------- | -------------- | ---------- | ---------- | --------------------------- | :----: |
| Squirrel    | Active   |    ∞     |   ∞    | None        | Computational  | PRF        | Auth, Unli | Easy                        |   ✅   |
| CryptoVerif | Active   |    ∞     |   ∞    | None        | Computational  | PRF        | Auth, Unli | Easy                        |   ✅   |
| EasyCrypt   | Active   |    ∞     |   ∞    | None        | Computational  | PRF        | Auth, Unli | Hard                        |   ✅   |
| Tamarin     | Active   |    ∞     |   ∞    | None        | Symbolic       | Hash       | Auth, ⚡RA | Easy (Auth,RA), Hard (Unli)  |   ✅   |
| Proverif    | Active   |    ∞     |   ∞    | None        | Symbolic       | Hash       | Auth, ⚡RA | Easy (Auth,RA), Hard (Unlo)  |  WIP   |



## Problem 2: Signed Diffie-Hellman

subfolder: [signedDH](signedDH/)

<!-- 
| Proverif | Tamarin | DY* | Squirrel | CryptoVerif | EasyCrypt |
| -------- | -------:| --- | -------- | ----------- | --------- |
| Easy     |    Easy | ?   | Easy  | Easy        | HARD      | -->

| Tool        | Attacker | Sessions | Agents | Compromises | Attacker Class | Primitives     | Properties | Difficulty ratings | Status |
| :---------- | -------- | :------: | :----: | ----------- | -------------- | -------------- | ---------- | ------------------ | :----: |
| Squirrel    | Active   |    ∞     |   ∞    | None        | Computational  | Hash, Sign     | Auth, FS   | Easy               |        |
| CryptoVerif | Active   |    ∞     |   ∞    | None        | Computational  | Hash, Sign     | Auth, FS   | Easy               |        |
| EasyCrypt   | Active   |    ∞     |   ∞    | None        | Computational  | Hash, Sign     | Auth, FS   | Hard               |        |
| Tamarin     | Active   |    ∞     |   ∞    | LTK         | Symbolic       | Hash, DH, Sign | Auth, FS   | Easy (Auth,FS)     |   ✅   |
| Proverif    | Active   |    ∞     |   ∞    | None        | Symbolic       | Hash, Sign     | Auth, FS   | Easy (Auth,FS)     |        |


> [!TIP]
> Possible extensions: LTK compromise (for Forward Secrecy) + Ephemeral compromise.
> * LTK compromise: does not really increase difficulty
> * Ephemeral compromise: OOS for CryptoVerif.



## Problem 3: Signed KEM

subfolder: [signedKEM](signedKEM/)

| Tool        | Attacker | Sessions | Agents | Compromises      | Attacker Class | Primitives              | Properties                 | Difficulty ratings | Status |
| :---------- | -------- | :------: | :----: | ---------------- | -------------- | ----------------------- | -------------------------- | ------------------ | :----: |
| Squirrel    | Active   |    ∞     |   ∞    | None             | Computational  | Hash, Sign              | Auth, FS                   | Easy               |        |
| CryptoVerif | Active   |    ∞     |   ∞    | None             | Computational  | Hash, Sign              | Auth, FS                   | Easy               |        |
| EasyCrypt   | Active   |    ∞     |   ∞    | None             | Computational  | Hash, Sign              | Auth, FS                   | Hard               |        |
| Tamarin     | Active   |    ∞     |   ∞    | LTK, EK, MAL_LTK | Symbolic       | Hash, DH, Sign, AsymEnc | Auth, FS, ⚡UKS, ⚡ReEncap | Easy               |   ✅   |
| Proverif    | Active   |    ∞     |   ∞    | None             | Symbolic       | Hash, Sign              | Auth, FS                   | Easy (Auth,FS)     |        |



## Problem 4: Signed DH+KEM

subfolder: [signedDH+KEM](signedDH+KEM/)

| Tool        | Attacker | Sessions | Agents | Compromises | Attacker Class | Primitives        | Properties        | Difficulty ratings | Status |
| :---------- | -------- | :------: | :----: | ----------- | -------------- | ----------------- | ----------------- | ------------------ | :----: |
| Squirrel    | Active   |    ∞     |   ∞    | None        | Computational  | Hash, Sign        | Auth, FS          | Easy               |        |
| CryptoVerif | Active   |    ∞     |   ∞    | None        | Computational  | Hash, Sign        | Auth, FS          | Easy               |        |
| EasyCrypt   | Active   |    ∞     |   ∞    | None        | Computational  | Hash, Sign        | Auth, FS          | Hard               |        |
| Tamarin     | Active   |    ∞     |   ∞    | LTK, EK     | Symbolic       | DH, Sign, AsymEnc | Auth, FS, Secrecy | Easy               |   ✅   |
| Proverif    | Active   |    ∞     |   ∞    | None        | Symbolic       | Hash, Sign        | Auth, FS          | Easy (Auth,FS)     |        |



## Problem 5: NTOR protocol

subfolder: [ntor](ntor/)

spec: https://spec.torproject.org/proposals/216-ntor-handshake.html

<!-- 
| Proverif | Tamarin | DY* | Squirrel | CryptoVerif | EasyCrypt |
| -------- | -------:| --- | -------- | ----------- | --------- |
| Easy     |    Easy | ?   | Medium?  | Easy        | HARD      | -->

| Tool        | Attacker | Sessions | Agents | Compromises | Attacker Class | Primitives | Properties        | Difficulty ratings | Status |
| :---------- | -------- | :------: | :----: | ----------- | -------------- | ---------- | ----------------- | ------------------ | :----: |
| Squirrel    | Active   |    ∞     |   ∞    | None        | Computational  | Hash, DH   | Auth, FS          | Easy               |        |
| CryptoVerif | Active   |    ∞     |   ∞    | None        | Computational  | Hash, DH   | Auth, FS          | Easy               |        |
| EasyCrypt   | Active   |    ∞     |   ∞    | None        | Computational  | Hash, DH   | Auth, FS          | Hard               |        |
| Tamarin     | Active   |    ∞     |   ∞    | LTK, EK     | Symbolic       | Hash, DH   | Auth, FS, Secrecy | Easy               |   ✅   |
| Proverif    | Active   |    ∞     |   ∞    | None        | Symbolic       | Hash, DH   | Auth, FS          | Easy               |        |

> [!TIP]
> Possible extensions: LTK compromise (for Forward Secrecy) + Ephemeral compromise.
> * LTK compromise: does not really increase difficulty
> * Ephemeral compromise: OOS for CryptoVerif.

> [!NOTE]
> * Shows that ntor is "harder" than signedDH, due to authentication through static DH keys, which implies authentication based on gDH+ROM.



## Problem 6: Simplified ACME

subfolder: [acme](acme/)

| Tool        | Attacker | Sessions | Agents | Compromises | Attacker Class | Primitives | Properties  | Difficulty ratings | Status |
| :---------- | -------- | :------: | :----: | ----------- | -------------- | ---------- | ----------- | ------------------ | :----: |
| Squirrel    | Active   |    ∞     |   ∞    | None        | Computational  | Sign       | Auth        | Easy               |        |
| CryptoVerif | Active   |    ∞     |   ∞    | None        | Computational  | Sign       | Auth        | Easy               |        |
| EasyCrypt   | Active   |    ∞     |   ∞    | None        | Computational  | Sign       | Auth        | Hard               |        |
| Tamarin     | Active   |    ∞     |   ∞    | None        | Symbolic       | Sign       | Auth, ⚡DEO  | Easy               |   ✅   |
| Proverif    | Active   |    ∞     |   ∞    | None        | Symbolic       | Sign       | Auth        | Easy               |        |



## Showcase

| Tool      | Case-study | Description       | Link                | Model                    |
| --------- | ---------- | ----------------- | ------------------- | ------------------------ |
| EasyCrypt | Kyber      | WIP               | WIP                 | WIP                      |                                                                  |
| Tamarin   | SPDM       | SPDM is a protocol that aims to provide platform security, for example for communicating hardware components or cloud computing scenarios. The standard is under development by the DMTF consortium, and supported by major industry players including Broadcom, Cisco, Dell, Google, HP, IBM, Intel, and NVIDIA. | [paper](https://eprint.iacr.org/2024/2047) | [model](https://github.com/ComprehensiveSPDM/TamarinSPDMAnalysis) |




# Primitives


Current primitive examples:
* Encrypt-Then-Mac is IND-CPA + INT-CTXT
* KEM+DEM is semantically secure as a PKE

Possible ideas:
* IND-CPA KEM from DH + ROM 
* play around DDH/CDH/gapDH
* biKEM from dualPRF + two IND-CPA KEM

Basic primitives are OOS for symbolic tools.

All primitives models in Squirrel will have a weaker attacker model (only asymptotic security, limitation being lifted in WIP)

## Encrypt-Then-Mac is IND-CPA + INT-CTXT

subfolder: [EtM-IND-CPA+CTXT](EtM-IND-CPA+CTXT/)

| Squirrel | CryptoVerif | EasyCrypt |
| --------:| ----------- |:--------- |
|  Medium? | Easy        | Easy     |

## KEM+DEM is semantically secure as a PKE

subfolder: [kemdem](kemdem/)

| Squirrel | CryptoVerif | EasyCrypt |
| --------:| ----------- |:--------- |
|  Medium? | Easy        | Easy     |


# Symmetric primitives

WIP

# Asymmetric primitives

WIP
# Acknowledgments

This work was initiated by the HACS workshop. The main contributors for the design of the problems set are: Manuel Barbosa (primitives), Cas Cremers (protocols), François Dupressoir (primitives and protocols), Charlie Jacomme (protocols), Aurora Naska (protocols), Trevor Perrin (main coordinator), Mike Rosulek (primitives). We additionally thank the following for their valuable feedback: Karthikeyan Bhargavan, Jonathan Katz, Devon Tuma, Bas Spitters, and Théophile Wallez. Further authorship attributions can be found in specific solutions.

