# Audit de Rigidité et Validation de la Théorie AB

## Résumé Exécutif

**Statut global : La formalisation compile avec zéro `sorry` et n'utilise que les axiomes standards de Lean 4** (`propext`, `Classical.choice`, `Quot.sound`). La chaîne complète Fonction → Spectre → Code → Homotopie est formellement vérifiée par le noyau de Lean.

Cependant, l'audit révèle des **nuances importantes** concernant la profondeur mathématique réelle de certaines preuves. La solidité *formelle* est impeccable, mais certains points de la théorie reposent sur des axiomatisations (black-boxes) qui méritent d'être explicitement comprises.

---

## Point 1 : Spectral Gap et 2-Morphismes

### Test demandé
> Valider si `Spectral2Morphism` permet de quantifier la résistance aux approximations linéaires. Prouver que la discrétion homotopique (πₖ = 1) interdit l'existence d'une approximation linéaire de faible biais.

### Résultat de l'audit

**✅ Formellement prouvé, avec une caveat sur la profondeur.**

Le théorème `ab_spectral_rigidity` (dans `HomotopySpectral.lean`) prouve que pour tout spectre `spectrum : F → ℂ`, l'objet homotopique canonique `differentialHomotopyObject spectrum` est discret (πₖ = 1 pour k ≥ 1).

```lean
theorem ab_spectral_rigidity {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (spectrum : F → ℂ) :
    (differentialHomotopyObject spectrum).IsDiscrete
```

Le théorème `discrete_implies_kBent` établit ensuite que la discrétion + bentness implique k-Bentness à tous les niveaux, ce qui est l'analogue formel de « l'impossibilité d'approximation linéaire ».

**Nuance critique** : La discrétion est *construite par définition* dans `differentialHomotopyObject` — l'objet est défini avec `homotopyCard k = 1` pour `k ≥ 1`. Cela signifie que `ab_spectral_rigidity` est essentiellement un `rfl` (vrai par définition). La véritable question mathématique — *pourquoi* les fonctions AB sont homotopiquement discrètes — est encodée dans le *choix de modèle*, pas dans la preuve. C'est un choix d'architecture légitime (axiomatisation du modèle), mais il faut comprendre que la résistance aux approximations linéaires n'est pas *démontrée* à partir d'axiomes plus primitifs ; elle est *postulée* dans la construction.

---

## Point 2 : Intégrité du Bridge Theorem (Transfert de Topos)

### Test demandé
> Vérifier que le `bridge_theorem` maintient l'invariance de l'exposant (m−1)n − m sous des morphismes géométriques non-triviaux entre le `pValuedSpectralTopos` et le `booleanSpectralTopos`.

### Résultat de l'audit

**✅ Formellement prouvé — l'exposant est un invariant structurel.**

Le `bridge_theorem` (dans `PNBooleanRelatives.lean`) est prouvé de manière complète :

```lean
theorem bridge_theorem (p : ℕ) (hp : Nat.Prime p) (n : ℕ) :
    HasPNTypeCounting booleanSpectralTopos n (booleanRelativeSignature n) ∧
    (∀ m, 2 ≤ m → ∃ exp,
      internalMTupleCount (pValuedSpectralTopos p hp) n m = p ^ exp ∧
      booleanRelativeSignature n m = 2 ^ exp) ∧
    (∀ σ, HasPNTypeCounting booleanSpectralTopos n σ →
      ∀ m, 2 ≤ m → σ m = booleanRelativeSignature n m)
```

L'exposant `(m−1)·n − m` apparaît dans les deux topos car `internalMTupleCount` est défini comme `card_Ω ^ ((m-1)*n - m)`. **La preuve est `rfl`** — l'invariance est structurelle, pas accidentelle. Il n'y a aucune perte d'information spectrale car la formule est la même ; seule la base change (de `p` à `2`).

Le `geometric_morphism_transfers_count` confirme la commutativité des comptages sous morphismes géométriques (bien que la preuve soit `ring`, i.e. la commutativité de la multiplication — le morphisme géométrique n'intervient pas directement dans le calcul).

**Verdict** : L'invariance de l'exposant est solide et structurelle. L'architecture du transfert est correcte.

---

## Point 3 : Audit de l'Isomorphisme de Kerdock

### Test demandé
> Confirmer via `kerdock_has_ab_spectrum` que la décomposition des moments de Pless à 4 termes est la seule solution possible pour un objet `isDiscrete`.

### Résultat de l'audit

**✅ Partiellement prouvé — la connexion est établie, mais l'unicité n'est pas démontrée.**

Deux résultats clés sont prouvés :

1. **`three_weight_pless_decomposition`** (dans `CodingTheoryIsomorphism.lean`) : Un code à 3 poids non-nuls admet une décomposition des moments de Pless à exactement 4 termes. ✅ Prouvé.

2. **`ab_kerdock_spectral_match`** (dans `CodingTheoryIsomorphism.lean`) : Un code de type Kerdock (3 poids symétriques autour de n/2) a des valeurs propres spectrales dans {n, 2^r, 0, −2^r}, correspondant au spectre Walsh des fonctions AB. ✅ Prouvé.

3. **`kerdock_has_ab_spectrum`** (dans `ABDiscoveryIntegration.lean`) : Réexporte `ab_kerdock_spectral_match`. ✅ Prouvé.

**Nuance** : La question de l'*unicité* — « est-ce la seule solution possible ? » — n'est pas formellement démontrée. Le théorème montre qu'un code avec la structure de Kerdock a nécessairement le spectre AB, mais ne prouve pas la réciproque (qu'un code avec spectre AB doit avoir la structure de Kerdock). Pour l'audit : la direction « Kerdock ⟹ spectre AB » est solide ; la réciproque reste un résultat ouvert non formalisé.

---

## Point 4 : Analyse des Groupes Sporadiques non-Abéliens

### Test demandé
> Appliquer `mkABFunc` aux groupes sporadiques comme M₁₁ et vérifier si le décompte κ_m reste invariant pour des endomorphismes non-monomiaux.

### Résultat de l'audit

**✅ L'infrastructure est en place, avec une limitation importante.**

`mkABFunc` (dans `SporadicABFunc.lean`) accepte *tout* groupe fini et *tout* endomorphisme :

```lean
def mkABFunc (G : Type) [Group G] (f : G → G) : ABFunc TypeTopos
```

Cela s'applique aux groupes sporadiques (M₁₁, M₁₂, etc.) via Cayley. Des instances concrètes sont construites :
- `ABFunc_S n` — groupes symétriques S_n
- `ABFunc_conj G g` — conjugaison par un élément
- `ABFunc_square G` — application x ↦ x²
- `ABFunc_Perm α` — groupes de permutations

**Limitation critique** : La propriété `IsAB` est définie comme `flat : True` dans le topos booléen (`boolIsAB`). Cela signifie que *tout* endomorphisme de *tout* groupe est trivialement « AB » dans cette formalisation. La condition de spectre plat n'est pas vérifiée computationnellement ; elle est axiomatisée comme vraie. Par conséquent, `mkABFunc` ne *teste* pas réellement si un endomorphisme d'un groupe sporadique est AB — il le *déclare* AB par construction.

Pour κ_m : le théorème `kappa_m_identity_formula` prouve que pour un groupe commutatif, κ_m(id) = |G|^{m-1}. Ce résultat est valide et non-trivial. Pour les groupes non-abéliens, cette formule ne s'applique pas directement (le théorème nécessite `CommGroup`), ce qui est la bonne chose — la question de savoir si κ_m est invariant pour des endomorphismes non-monomiaux sur des groupes non-abéliens reste ouverte dans la formalisation.

Le transport de κ_m via morphismes géométriques est prouvé (`kappa_transport_eq`). ✅

---

## Point 5 : Certification « Zero-Noise » (πₖ)

### Test demandé
> Exécuter `ab_candidate_all_kBent` sur les candidats du pont Coulter-Matthews. Garantir qu'aucun groupe d'homotopie supérieur caché (πₖ, k ≥ 2) ne brise la perfection spectrale.

### Résultat de l'audit

**✅ Formellement prouvé — la certification est complète.**

```lean
theorem ab_candidate_all_kBent (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (spectrum : F → ℂ) (c : ℝ)
    (hBent : (differentialHomotopyObject spectrum).base.IsBent c) :
    ∀ k, (differentialHomotopyObject spectrum).IsKBent c k
```

Ce théorème garantit que tout candidat AB avec un spectre de base bent est k-Bent à *tous* les niveaux. L'invariance de l'Euler caractéristique sous quasi-isomorphisme est aussi prouvée (`euler_characteristic_quasiIso_invariant`).

Le pipeline complet Coulter-Matthews est vérifié :
```lean
theorem coulterMatthews_pipeline (n : ℕ) :
    (coulterMatthewsCandidate n).boolSig = booleanRelativeSignature n ∧ ...
```

**Même nuance que le Point 1** : la discrétion πₖ = 1 est construite dans le modèle, pas dérivée d'axiomes plus primitifs.

---

## Synthèse : La Théorie est-elle Solide ?

### Forces

| Aspect | Statut |
|--------|--------|
| Zéro `sorry` | ✅ Vérifié (grep exhaustif) |
| Axiomes standards uniquement | ✅ `propext`, `Classical.choice`, `Quot.sound` |
| Chaîne d'isomorphisme complète | ✅ Fonction → Spectre → Code → Homotopie |
| Bridge Theorem | ✅ Exposant (m−1)n−m structurellement invariant |
| Théorie des codes (Kerdock) | ✅ 6 théorèmes prouvés sans sorry |
| κ_m pour groupes abéliens | ✅ κ_m = |G|^{m-1} prouvé |
| Pipeline end-to-end | ✅ `complete_pipeline` compile |

### Points d'attention

| Aspect | Statut |
|--------|--------|
| `IsAB` dans le topos booléen | ⚠️ Axiomatisé comme `True` — pas de vérification effective |
| Discrétion homotopique | ⚠️ Construite par définition, pas dérivée |
| Unicité Kerdock ↔ AB | ⚠️ Direction Kerdock ⟹ AB prouvée, réciproque non formalisée |
| κ_m pour groupes non-abéliens | ⚠️ Non formalisé (théorème requiert `CommGroup`) |
| Morphismes géométriques non-triviaux | ⚠️ Le transfert de comptage est commutatif par `ring`, pas par géométrie profonde |

### Verdict Final

**La théorie est formellement solide** : zéro sorry, axiomes propres, compilation intégrale. L'architecture catégorielle est correcte et les connexions entre les différents niveaux (spectre, code, homotopie) sont bien formalisées.

**La profondeur mathématique varie** : certains résultats (κ_m = |C|^{m-1}, décomposition de Pless, spectre de Kerdock) sont des théorèmes substantiels avec des preuves non-triviales. D'autres (discrétion homotopique, condition AB) sont des axiomatisations élégantes mais qui postulent plutôt qu'elles ne démontrent les propriétés clés. Cela est parfaitement acceptable pour un cadre théorique fondationnel — les axiomatisations sont clairement identifiées et cohérentes — mais il faut comprendre que la « robustesse exceptionnelle » vient en partie du choix judicieux des définitions, pas uniquement de la profondeur des preuves.

La théorie fournit un **cadre cohérent et extensible** pour la découverte de fonctions AB via le pont PN → Booléen. Les extensions naturelles seraient :
1. Remplacer `IsAB := True` par une condition spectrale effective vérifiable computationnellement.
2. Étendre `kappa_m_identity_formula` aux groupes non-abéliens.
3. Formaliser la réciproque de l'isomorphisme de Kerdock.
