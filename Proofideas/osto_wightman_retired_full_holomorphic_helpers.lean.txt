/-!
# Retired Full-Holomorphic Base-Step Helpers

This file records the private helper block removed from
`Wightman/Reconstruction/WickRotation/OSToWightman.lean` on 2026-03-15.

Why it was retired:

- the live public base-step surface is now the time-parametric theorem
  `schwinger_continuation_base_step_timeParametric`;
- the downstream continuation chain still consumes only the private upgrade
  theorem `schwinger_continuation_base_step_full`;
- the deleted helpers were staging for an older full-holomorphic/Osgood route
  and were no longer referenced by the production chain.

Retired declarations:

- `preimage_update_time_tubeDomain_flatPositiveTimeDiffReal`
- `preimage_update_spatial_tubeDomain_flatPositiveTimeDiffReal`
- `differentiableOn_tubeDomain_flatPositiveTimeDiffReal_of_slices`
- `differentiableOn_toDiffFlat_of_acrone_holo`
- `differentiableOn_of_toDiffFlat_acrone_holo`
- `differentiableOn_twoPoint_timeDiffFlatWitness`
- `neg_I_mul_flattenCfg_wickRotate_secondTime_eq`
- `twoPoint_timeDiffFlatWitness_apply_wickRotate`
- `differentiableOn_OSInnerProductTimeShiftHolomorphicValue_local`
- `schwinger_continuation_base_step_of_flatWitness`

The `FlatPositiveTimeDiffReal` witness type, the public time-parametric base
step, the private spatial-upgrade theorem, and the private
`schwinger_continuation_base_step_full` theorem remain in production.
-/
