# V22 Empirical Mediator Process

This note describes the full V22 empirical process as implemented in the ASLMT
experiment:

```text
aslmt_v22_perceptual_localglobal_dynamic_infinite
```

The goal is not merely to train a model with good predictive performance.  The
goal is to test whether a model can learn an operational incidence structure:

```text
what information is missing,
which interface can recover it,
how a finite mediator carries it,
and how that mediator closes the remaining ambiguity.
```

The experiment is synthetic because the hidden variables, interfaces, residual
ambiguities, and failure modes can be exactly reconstructed and verified.

## 1. World Structure

Each example is rendered from a finite hidden world.

The hidden variables are:

```text
h : hidden class / local position
k : hidden orientation bit
```

The target object depends on both `h` and `k`.

In the renderer:

```text
h determines the hidden position inside the occluded region
k determines the orientation of the hidden target
```

The visible image contains an occluder and does not reveal the complete target.
The cue contains a marker from which `h` can be recovered.

Thus the task has two different kinds of missing information:

```text
image alone loses h
cue alone loses k
the hidden target requires both h and k
```

## 2. Interfaces and Incidence

The experiment is an operational version of an incidence algebra.

At the finite algebraic level, one can describe the structure as:

```text
R_sigma = required target distinctions
C_j     = confusions induced by interface j
L_j     = R_sigma ∩ C_j
L_res   = common residual loss
rho     = size of the residual
```

In words:

```text
R_sigma records which pairs must be distinguished.
C_j records which pairs interface j confuses.
L_j records which required distinctions are lost by interface j.
L_res records which distinctions remain lost by the available family.
rho measures the remaining residual.
```

The model is not only learning to predict.  It is learning, behaviorally, which
interfaces preserve or lose which distinctions, and how to select the next
interface needed to close the residual.

## 3. The Active Query Mechanism

The experiment includes two possible actions, interpreted as two possible
interfaces to query.

There is a deterministic but nontrivial policy:

```text
policy(h) : {0, ..., n_classes - 1} -> {0, 1}
```

The environment response is:

```text
res_bit = k if action == policy(h)
res_bit = 0 otherwise
```

So the response bit reveals `k` only when the model chooses the correct
interface/action.

The required operational chain is therefore:

```text
cue -> recover h
h -> choose the correct interface/action
correct action -> response bit reveals k
image + h-mediated information + response bit -> hidden target
```

This is active information recovery, not passive prediction.

## 4. The Finite Mediator `z`

The model has a discrete mediator:

```text
z : Fin z_classes
```

The model is constrained so that the query reads the discrete mediator rather
than an unconstrained continuous hidden vector:

```text
query_logits := f(one_hot(argmax(z_logits.detach())))
```

This matters because the action path is forced through a finite object.

The intended positive case is:

```text
z_classes = n_classes
```

In this case, `z` has enough capacity to represent the relevant hidden class
`h`.

The intended negative case is:

```text
z_classes < n_classes
```

In that case, two different hidden classes must collide under the finite
mediator.  The minproof verifier checks that such a collision forces a paired
discrimination failure.

## 5. Training Losses

The training objective contains several components.

The main model loss includes:

```text
lossA_seg       segmentation/readout loss for the hidden target
lossA_z         supervision of the finite mediator z
lossA_q         supervision of the query/action policy
lossA_pos       position consistency loss
lossA_rank_img  image-gate pair-ranking constraint
lossA_rank_cue  cue-gate pair-ranking constraint
```

The baselines are trained separately:

```text
modelB_img : image-only baseline
modelB_cue : cue-only baseline
```

They are useful precisely because the verifier checks that they do not close the
task in the forbidden marginal regimes.

The rank losses are not generic performance metrics.  They are aligned with the
certificate checks: they train the model on the same paired-context structure
later used by the structural proofpack and verifier.

## 6. Expected Positive Dynamics

In the positive capacity case:

```text
n_classes = 8
z_classes = 8
```

the expected dynamics are:

```text
rank_img/rank_cue collapse toward zero
z becomes accurate
query/action becomes accurate
response bit becomes informative
segmentation/readout becomes clean
```

A typical successful trajectory therefore has the shape:

```text
rank constraints close first
z and q stabilize
the hidden target readout improves
IID and OOD remain aligned
```

This is the empirical signature that the model is learning the operational
incidence structure rather than merely exploiting one marginal shortcut.

## 7. Marginal No-Go Verification

The marginal no-go verifier checks the task structure independently of the
training loss.

It recomputes pairs such that:

```text
same image, different hidden target
same cue, different hidden target
```

This verifies that neither marginal interface alone contains the full
distinction required by the target.

In conceptual terms:

```text
image-only access leaves a residual
cue-only access leaves a residual
the target requires a mediated joint process
```

A passing marginal no-go certificate means:

```text
the marginal impossibility is real in the generated world
```

not merely a training artifact.

## 8. Minproof Verification

The minproof verifier checks the finite-capacity lower bound.

When:

```text
z_classes < n_classes
```

the verifier searches for two different hidden classes:

```text
h0 != h1
```

that collide under:

```text
argmax(z_logits)
```

It then recomputes the corresponding examples and checks that the collision
forces failure: the decoder receives the same relevant mediated value where it
would need different ones.

Thus the verifier is not merely observing lower accuracy.  It checks a specific
collision witness.

The meaning is:

```text
too-small z -> collision -> forced paired-discrimination failure
```

This is the empirical analogue of a finite mediator lower bound.

## 9. Structural Proofpack Verification

The structural verifier recomputes the paired checks from the certificate.

It tests:

```text
image barrier
cue barrier
modelA image-gate pair discrimination
modelA cue-gate pair discrimination
image-only baseline failure
cue-only baseline failure
z-ablation failure
z-swap follow behavior
z-swap not preserving the original target
```

The important intervention checks are:

```text
ablation:
  removing z should break the mediated success

swap:
  swapping z should make the prediction follow the swapped mediator
```

This prevents the model from passing only through correlation.  The mediator has
to be load-bearing.

## 10. Meaning of `z = n` Versus `z < n`

The experiment is organized around the contrast:

```text
z = n
```

versus:

```text
z < n
```

The expected pattern is:

```text
z = n:
  enough finite capacity;
  mediator can separate hidden modes;
  closure can pass.

z < n:
  insufficient finite capacity;
  hidden modes collide;
  minproof collision witness exists;
  paired discrimination is forced to fail.
```

This is why the numerical logs matter only together with the verifiers.

The training logs show whether the model is moving toward closure.  The
certificates and verifiers decide whether the closure claim actually holds.

## 11. Relation to World Models

The experiment attacks a specific weakness of ordinary latent representations.

A standard predictive latent may be useful, but usefulness alone does not say:

```text
which distinctions are lost,
which information is missing,
which interface can recover it,
whether the latent has enough finite capacity,
whether smaller latents must fail,
whether the latent is causally load-bearing.
```

V22 tests a stronger object:

```text
a finite mediator that supports active recovery of missing information
```

The model must learn not only a representation, but an access policy:

```text
detect the relevant hidden class through cue
select the interface/action determined by it
receive the response that reveals the missing bit
use the mediator and response to close the hidden target
```

This is why the experiment is about navigation by closure, not passive
prediction.

## 12. Full Process Summary

The full V22 process is:

```text
1. Generate a finite perceptual world with hidden variables h and k.
2. Render image and cue interfaces with controlled lost distinctions.
3. Define a nontrivial policy policy(h) selecting the correct interface.
4. Return res_bit = k only when the chosen interface is correct.
5. Force the query/action path through a finite mediator z.
6. Train the model with segmentation, z, query, position, and rank losses.
7. Train image-only and cue-only baselines.
8. Certify marginal no-go: each marginal alone loses a required distinction.
9. Certify minproof: z<n forces collisions and paired failure.
10. Certify structural behavior: gates, baselines, ablation, swap.
11. Verify certificates independently from training.
12. Interpret success as learned incidence algebra and mediated closure.
```

## 13. Core Claim

The core empirical claim of V22 is:

```text
The model learns an operational incidence algebra:
it identifies missing information,
selects the interface that can recover it,
uses a finite mediator to carry it,
and closes the target distinction only when the mediator has sufficient capacity.
```

This is stronger than saying that the model learned a useful latent.

It is a certificate-oriented claim:

```text
marginal no-go
+ finite-capacity lower bound
+ mediated closure
+ intervention-tested dependence
```

## 14. Protocol-Level Reading

The most important object in V22 is the protocol.

The protocol is designed so that each theoretical notion has an empirical
counterpart:

```text
theory:
  required distinction
empirical protocol:
  two generated examples with different hidden targets

theory:
  active interface loses a distinction
empirical protocol:
  same image or same cue, but different hidden target

theory:
  residual remains open
empirical protocol:
  a marginal verifier can exhibit an unresolved pair

theory:
  finite mediator closes the residual
empirical protocol:
  z=n allows the model to separate the relevant hidden modes

theory:
  insufficient mediator dimension cannot close
empirical protocol:
  z<n produces a collision witness and forced paired failure

theory:
  mediator is not a decorative variable
empirical protocol:
  z-ablation breaks success and z-swap makes the output follow the swapped z
```

The protocol therefore does not merely report performance.  It builds an
audit-able bridge from the abstract residual-closure vocabulary to concrete
finite evidence.

## 15. What the Protocol Adds Beyond the Abstract Theory

The abstract theory proves the shape:

```text
residual witness
mediated closure
irreducible mediator
finite dimension / lower bound
```

V22 adds an empirical and operational layer:

```text
perceptual rendering
active interface selection
action-conditioned information recovery
finite-capacity training
IID/OOD evaluation
episode/context-level certificates
independent verifiers
intervention tests on the mediator
```

The abstract theory says what it means for a mediator to close a residual.

The V22 protocol tests whether a learned system can actually:

```text
1. encounter a missing distinction;
2. recover the hidden class needed to choose an interface;
3. select the correct interface/action;
4. obtain the missing response bit;
5. use the finite mediator and the response to close the target;
6. fail in the predicted way when mediator capacity is too small.
```

This is the extra empirical content.

The experiment is not only a witness of closure.  It is a witness of active
closure:

```text
the system learns where the missing information is,
how to retrieve it,
and how to use it.
```

## 16. Why the Verifiers Matter More Than the Loss

The training log is useful because it shows a plausible closure trajectory:

```text
rank losses decrease
z loss decreases
query loss decreases
segmentation/readout improves
```

But the loss does not certify the claim.

The claim is certified only by the verifiers:

```text
marginal no-go verifier:
  checks that the marginal barriers are real

minproof verifier:
  checks that z<n creates collision witnesses and forced failures

structural verifier:
  checks model success, baseline failure, ablation failure, and swap-follow
```

Thus the loss is a training diagnostic, while the proofpack and verifiers are
the empirical certificate.

## 17. Protocol Summary as a Theory Bridge

The bridge can be summarized as:

```text
abstract R1/R2 layer:
  residual distinction invisible to active interfaces
  finite mediator closes it
  smaller mediator cannot close it

V22 empirical layer:
  image/cue marginal barriers instantiate lost distinctions
  z is the finite mediator
  z=n is the sufficient-capacity case
  z<n is the collision/lower-bound case
  action selection tests whether the mediator is operational
  ablation/swap tests whether the mediator is causal/load-bearing
```

So the central question for judging V22 is:

```text
Does the protocol faithfully instantiate the theory's residual, mediator,
lower-bound, and irreducibility ideas in a finite perceptual world?
```

The point of the experiment is that this question is not answered by trust.  It
is answered by generated examples, proofpack records, and independent
verification scripts.
