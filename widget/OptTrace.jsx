import * as React from "react";
const e = React.createElement;

export default function (props) {
  const steps = props.steps || [];
  const [idx, setIdx] = React.useState(steps.length - 1);
  const sel = steps[idx];

  const prev = () => setIdx(Math.max(0, idx - 1));
  const next = () => setIdx(Math.min(steps.length - 1, idx + 1));

  React.useEffect(() => {
    const handler = (ev) => {
      if (ev.key === "ArrowLeft" || ev.key === "k") prev();
      if (ev.key === "ArrowRight" || ev.key === "j") next();
    };
    document.addEventListener("keydown", handler);
    return () => document.removeEventListener("keydown", handler);
  });

  const btnStyle = {
    padding: "2px 10px",
    cursor: "pointer",
    border: "1px solid var(--vscode-button-border, var(--vscode-panel-border))",
    borderRadius: "3px",
    background: "var(--vscode-button-secondaryBackground, transparent)",
    color: "var(--vscode-button-secondaryForeground, inherit)",
    fontSize: "14px",
  };

  return e(
    "div",
    {},
    // Controls row
    e(
      "div",
      {
        style: {
          display: "flex",
          gap: "4px",
          marginBottom: "8px",
          alignItems: "center",
        },
      },
      e(
        "button",
        { onClick: prev, disabled: idx === 0, style: btnStyle },
        "\u25C0"
      ),
      e(
        "select",
        {
          value: idx,
          onChange: (ev) => setIdx(Number(ev.target.value)),
          style: {
            flex: 1,
            fontSize: "12px",
            padding: "2px 4px",
            background: "var(--vscode-dropdown-background)",
            color: "var(--vscode-dropdown-foreground)",
            border: "1px solid var(--vscode-dropdown-border)",
          },
        },
        steps.map((s, i) =>
          e(
            "option",
            { key: i, value: i },
            (s.changed ? "\u2713 " : "  ") + s.pass
          )
        )
      ),
      e(
        "button",
        {
          onClick: next,
          disabled: idx === steps.length - 1,
          style: btnStyle,
        },
        "\u25B6"
      ),
      e(
        "span",
        {
          style: {
            fontSize: "11px",
            opacity: 0.6,
            whiteSpace: "nowrap",
            marginLeft: "4px",
          },
        },
        idx + 1 + "/" + steps.length
      )
    ),
    // MIR content
    sel &&
      e(
        "pre",
        {
          style: {
            margin: 0,
            padding: "10px",
            overflow: "auto",
            maxHeight: "70vh",
            fontSize: "13px",
            lineHeight: "1.5",
            whiteSpace: "pre-wrap",
            fontFamily: "var(--vscode-editor-font-family)",
            background: "var(--vscode-editor-background)",
            border: "1px solid var(--vscode-panel-border)",
            borderRadius: "4px",
          },
        },
        sel.expr
      )
  );
}
