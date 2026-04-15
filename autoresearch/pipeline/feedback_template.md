## Compilation Failed

Your code failed to compile. Here are the errors:

### Raw Errors
```
{errors}
```

### Analysis
{parsed_issues}

### Tips for Iteration {iteration}/{total}
- Read the error messages carefully -- Lean's errors are precise
- Common fixes:
  - Type mismatch: check your function signatures and return types
  - Tactic failed: try a different proof strategy
  - Unknown identifier: check imports (`import SM83`) and namespace (`namespace AutoResearch`)
  - `native_decide` timeout: your type might be too large -- use manual tactics instead
  - `sorry` is acceptable as a placeholder if you cannot prove something
- If the same error persists across iterations, try a fundamentally different modeling approach
- Simplify: fewer theorems that compile is better than many that don't

Output your complete, corrected Solution.lean inside a ```lean code block.
