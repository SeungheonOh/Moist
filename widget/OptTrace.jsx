import * as React from "react";
const e = React.createElement;

/** Simple line-based diff: returns array of {type, text} where type is "same", "add", or "del". */
function diffLines(oldStr, newStr) {
  const oldLines = oldStr.split("\n");
  const newLines = newStr.split("\n");
  const m = oldLines.length, n = newLines.length;

  // Myers-like: build edit path via LCS
  const max = m + n;
  const v = new Int32Array(2 * max + 1);
  const trace = [];
  for (let d = 0; d <= max; d++) {
    const snap = new Int32Array(v);
    trace.push(snap);
    for (let k = -d; k <= d; k += 2) {
      let x;
      if (k === -d || (k !== d && v[k - 1 + max] < v[k + 1 + max])) {
        x = v[k + 1 + max];
      } else {
        x = v[k - 1 + max] + 1;
      }
      let y = x - k;
      while (x < m && y < n && oldLines[x] === newLines[y]) { x++; y++; }
      v[k + max] = x;
      if (x >= m && y >= n) {
        // Backtrack
        const ops = [];
        let cx = m, cy = n;
        for (let bd = d; bd > 0; bd--) {
          const pv = trace[bd - 1];
          const ck = cx - cy;
          let px;
          if (ck === -bd || (ck !== bd && pv[ck - 1 + max] < pv[ck + 1 + max])) {
            px = pv[ck + 1 + max];
          } else {
            px = pv[ck - 1 + max] + 1;
          }
          const py = px - ck;
          while (cx > px && cy > py) { cx--; cy--; ops.push({ type: "same", text: oldLines[cx] }); }
          if (cy > py) { cy--; ops.push({ type: "add", text: newLines[cy] }); }
          else if (cx > px) { cx--; ops.push({ type: "del", text: oldLines[cx] }); }
        }
        while (cx > 0 && cy > 0) { cx--; cy--; ops.push({ type: "same", text: oldLines[cx] }); }
        while (cy > 0) { cy--; ops.push({ type: "add", text: newLines[cy] }); }
        while (cx > 0) { cx--; ops.push({ type: "del", text: oldLines[cx] }); }
        ops.reverse();
        return ops;
      }
    }
  }
  // Fallback: everything changed
  return [
    ...oldLines.map(text => ({ type: "del", text })),
    ...newLines.map(text => ({ type: "add", text })),
  ];
}

export default function (props) {
  const steps = props.steps || [];
  const [idx, setIdx] = React.useState(steps.length - 1);
  const [showDiff, setShowDiff] = React.useState(true);
  const sel = steps[idx];
  const prevStep = idx > 0 ? steps[idx - 1] : null;

  const prev = () => setIdx(i => Math.max(0, i - 1));
  const next = () => setIdx(i => Math.min(steps.length - 1, i + 1));

  React.useEffect(() => {
    const handler = (ev) => {
      if (ev.key === "ArrowLeft" || ev.key === "k") prev();
      if (ev.key === "ArrowRight" || ev.key === "j") next();
      if (ev.key === "d") setShowDiff(d => !d);
    };
    document.addEventListener("keydown", handler);
    return () => document.removeEventListener("keydown", handler);
  });

  const diff = React.useMemo(() => {
    if (!showDiff || !prevStep || !sel) return null;
    if (prevStep.expr === sel.expr) return [];
    return diffLines(prevStep.expr, sel.expr);
  }, [idx, showDiff]);

  const btnStyle = {
    padding: "2px 10px",
    cursor: "pointer",
    border: "1px solid var(--vscode-button-border, var(--vscode-panel-border))",
    borderRadius: "3px",
    background: "var(--vscode-button-secondaryBackground, transparent)",
    color: "var(--vscode-button-secondaryForeground, inherit)",
    fontSize: "14px",
  };

  const badgeStyle = (changed) => ({
    fontSize: "11px",
    padding: "1px 6px",
    borderRadius: "3px",
    background: changed
      ? "var(--vscode-testing-iconPassed, #2ea04366)"
      : "var(--vscode-badge-background, #555)",
    color: changed
      ? "var(--vscode-testing-passForeground, #73c991)"
      : "var(--vscode-badge-foreground, #ccc)",
    marginLeft: "8px",
  });

  // Group options by iteration
  const options = steps.map((s, i) => {
    const isIterStart = s.pass.includes(": ANF");
    const prefix = s.changed ? "\u2713 " : "  ";
    return e("option", {
      key: i, value: i,
      style: isIterStart ? { fontWeight: "bold" } : {},
    }, prefix + s.pass);
  });

  const renderDiff = () => {
    if (!diff) return null;
    if (diff.length === 0) {
      return e("div", {
        style: { padding: "10px", opacity: 0.5, fontStyle: "italic" },
      }, "No changes");
    }
    return e("pre", {
      style: {
        margin: 0, padding: "10px", overflow: "auto", maxHeight: "70vh",
        fontSize: "13px", lineHeight: "1.5",
        fontFamily: "var(--vscode-editor-font-family)",
        background: "var(--vscode-editor-background)",
        border: "1px solid var(--vscode-panel-border)",
        borderRadius: "4px",
      },
    }, diff.map((op, i) => {
      const color =
        op.type === "add" ? "rgba(50, 180, 80, 0.25)" :
        op.type === "del" ? "rgba(220, 60, 60, 0.25)" :
        "transparent";
      const marker =
        op.type === "add" ? "+ " :
        op.type === "del" ? "- " :
        "  ";
      return e("div", {
        key: i,
        style: { background: color, whiteSpace: "pre-wrap" },
      }, marker + op.text);
    }));
  };

  const renderFull = () => {
    if (!sel) return null;
    return e("pre", {
      style: {
        margin: 0, padding: "10px", overflow: "auto", maxHeight: "70vh",
        fontSize: "13px", lineHeight: "1.5", whiteSpace: "pre-wrap",
        fontFamily: "var(--vscode-editor-font-family)",
        background: "var(--vscode-editor-background)",
        border: "1px solid var(--vscode-panel-border)",
        borderRadius: "4px",
      },
    }, sel.expr);
  };

  return e("div", {},
    // Controls
    e("div", {
      style: { display: "flex", gap: "4px", marginBottom: "6px", alignItems: "center" },
    },
      e("button", { onClick: prev, disabled: idx === 0, style: btnStyle }, "\u25C0"),
      e("select", {
        value: idx,
        onChange: (ev) => setIdx(Number(ev.target.value)),
        style: {
          flex: 1, fontSize: "12px", padding: "2px 4px",
          background: "var(--vscode-dropdown-background)",
          color: "var(--vscode-dropdown-foreground)",
          border: "1px solid var(--vscode-dropdown-border)",
        },
      }, options),
      e("button", { onClick: next, disabled: idx === steps.length - 1, style: btnStyle }, "\u25B6"),
      e("span", {
        style: { fontSize: "11px", opacity: 0.6, whiteSpace: "nowrap", marginLeft: "4px" },
      }, idx + 1 + "/" + steps.length),
    ),
    // Pass info + view toggle
    sel && e("div", {
      style: { display: "flex", alignItems: "center", marginBottom: "6px", gap: "8px" },
    },
      e("strong", { style: { fontSize: "13px" } }, sel.pass),
      e("span", { style: badgeStyle(sel.changed) }, sel.changed ? "changed" : "unchanged"),
      e("button", {
        onClick: () => setShowDiff(d => !d),
        style: {
          ...btnStyle, fontSize: "11px", padding: "1px 8px", marginLeft: "auto",
        },
      }, showDiff ? "Full" : "Diff"),
    ),
    // Content
    showDiff && prevStep ? renderDiff() : renderFull(),
  );
}
