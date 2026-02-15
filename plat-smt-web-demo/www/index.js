import init, { Repl } from "./pkg/plat_smt_web_demo.js";

(async () => {
    await init();
    exec();
})();

const exec = () => {
    const html = String.raw;

    const createElementFromHtml = (html) => {
        const template = document.createElement("template");
        template.innerHTML = html.trim();
        return template.content.firstElementChild;
    };

    const element = (value) => {
        return createElementFromHtml(html`
        <div class="card">
          <p style="white-space: pre-wrap" class="err">${value.err}</p>
          <p style="white-space: pre-wrap">${value.out}</p>
        </div>
      `);
    }

    const result = document.querySelector("div.results");
    const textarea = document.querySelector("textarea#text");

    textarea.value = `(declare-const x Bool)\n(assert (not x))\n(check-sat)\n(get-model)`;

    const run = () => {
        const input = textarea.value;
        const value = Repl.eval(input);
        result.replaceChildren(element(value));
    };

    document.addEventListener("keydown", (e) => {
        if (e.key === "Enter") {
            run();
        }
    });

    document.querySelector("button.run").addEventListener("click", () => run());

    document.querySelector("button.clear").addEventListener("click", () => {
        textarea.value = ""
        run()
    });
};