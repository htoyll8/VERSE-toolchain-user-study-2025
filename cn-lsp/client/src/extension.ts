import * as vsc from "vscode";
import * as ct from "vscode-languageclient/node";

import fs from "fs";
import child_process from "child_process";

let client: ct.LanguageClient;

type Maybe<T> = T | null;

export function activate(context: vsc.ExtensionContext): void {
    const serverPath = findServer(context);
    if (serverPath === null) {
        vsc.window.showErrorMessage("CN client: unable to find CN server");
        throw Error;
    }
    const logFile = context.asAbsolutePath("./server-log.txt");
    const serverOptions: ct.Executable = {
        command: serverPath,
        args: [logFile],
        // In the future, we may want to define the `transport` field here,
        // perhaps as `ct.TransportKind.stdio`, but doing so appends a
        // command-line flag to the server invocation that the server doesn't
        // recognize. Leaving `transport` undefined seems to result in
        // communication via `stdio` (and no extra flag), which is what we
        // currently want anyway
    };

    const clientOptions: ct.LanguageClientOptions = {
        // Send the server messages about C files
        documentSelector: [{ scheme: "file", language: "c" }],
    };

    // I'm not sure how this value's semantics differs from that of
    // `clientName`, below, but I think it's intended to be a single word,
    // perhaps with hyphens/underscores, and should match the "namespace" we use
    // for this client's contributions. For example, if we contribute a property
    // "foo", we should define it (in package.json) as "CN.foo".
    const clientID: string = "CN";

    // A human-readable identifier for this package. I don't know the entirety
    // of how this information is used, but it at least appears in some error
    // messages displayed to the user, suffixed by " client".
    const clientName: string = "CN";

    client = new ct.LanguageClient(
        clientID,
        clientName,
        serverOptions,
        clientOptions
    );

    vsc.commands.registerCommand("CN.runOnFile", () => {
        const req = new ct.RequestType("$/runCN");

        const activeEditor = vsc.window.activeTextEditor;
        if (activeEditor === undefined) {
            vsc.window.showErrorMessage("CN client: no file currently open");
            return;
        }
        const doc = activeEditor.document;

        const params: ct.DidSaveTextDocumentParams = {
            textDocument: {
                uri: doc.uri.toString(),
            },
        };
        client.sendRequest(req, params);
    });

    client.start();
    console.log("started client");
}

export function deactivate(): Thenable<void> | undefined {
    if (!client) {
        return undefined;
    } else {
        return client.stop();
    }
}

function findServer(context: vsc.ExtensionContext): Maybe<string> {
    // Is it defined in $CN_LSP_SERVER?
    console.log("Looking in $CN_LSP_SERVER");
    console.log(process.env);
    let envPath = process.env.CN_LSP_SERVER;
    if (envPath !== undefined) {
        return envPath;
    }

    // Is it in a sibling directory? We expect this to hold in debug settings,
    // i.e. when the extension is running in a development host window.
    console.log("Looking in sibling directory");
    let siblingPath = context.asAbsolutePath("../server/bin/debug-server");
    if (fs.existsSync(siblingPath)) {
        return siblingPath;
    }

    // Is it on $PATH?
    console.log("Looking on $PATH");
    const out = child_process.spawnSync("which", ["cn-lsp-server"], {
        encoding: "utf-8",
    });
    if (out.status === 0) {
        return out.stdout.trim();
    }

    return null;
}
