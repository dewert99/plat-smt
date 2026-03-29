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

    const element = () => {
        return createElementFromHtml(html`
        <div class="card">
          <p style="white-space: pre-wrap" class="err">${repl.err()}</p>
          <p style="white-space: pre-wrap">${repl.out()}</p>
        </div>
      `);
    }

    const errElement = () => {
        return createElementFromHtml(html`
        <div class="card">
          <p style="white-space: pre-wrap" class="err">${"An internal error occurred, please refresh the page"}</p>
        </div>
      `);
    }

    const result = document.querySelector("div.results");
    const textarea = document.querySelector("textarea#text");
    let repl = Repl.new();
    let lastInput = ""

    textarea.value = `(declare-const x Bool)\n(assert (not x))\n(check-sat)\n(get-model)`;

    const run = (forceRefresh) => {
        const input = textarea.value;
        const addedParenToEnd = lastInput.length < input.length && input.startsWith(lastInput) && input.substring(lastInput.length).includes(')');
        console.log({input, lastInput, addedParenToEnd})
        lastInput = input;
        if (addedParenToEnd || forceRefresh) {
            try {
                const replace = repl.set_input(input);
                console.log({replace})
                if (replace) {
                    result.replaceChildren(element());
                }
            } catch (e) {
                console.error(e.message)
                result.replaceChildren(errElement())
            }
        }

    };

    document.addEventListener("keydown", (e) => {
        run(e.key === "Enter" && e.ctrlKey);
    });

    document.querySelector("button.run").addEventListener("click", () => run(true));

    document.querySelector("button.clear").addEventListener("click", () => {
        textarea.value = ""
        run(true)
    });
};