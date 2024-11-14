// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import path from 'path';
//import fs from 'fs';
import fsPromises from 'fs/promises';
import crypto from 'crypto';
import * as vscode from 'vscode';

function runTerminalAsync(opts: vscode.TerminalOptions): Promise<vscode.TerminalExitStatus> {
    const term = vscode.window.createTerminal(opts);
    term.show();
    return new Promise((resolve, reject) => {
        const token = vscode.window.onDidCloseTerminal((closedTerm) => {
            if (closedTerm === term) {
                token.dispose();
                if (term.exitStatus == null) {
                    reject('terminal closed with no exit status');
                    return;
                }
                resolve(term.exitStatus);
            }
        });
    });
}


// `SingletonWebViewPanel` is based on `CatCodingPanel` from `webview-sample`
// in https://github.com/microsoft/vscode-extension-samples, used under the
// following license:
//
// MIT License
//
// Copyright (c) 2015 - present Microsoft Corporation
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

// Helper for managing the webview panel.  At most one such panel can exist at
// a time.
//
class SingletonWebViewPanel {
    /**
     * Track the currently panel. Only allow a single panel to exist at a time.
     */
    public static currentPanel: SingletonWebViewPanel | undefined;

    public static readonly viewType = 'coqSynthesis';

    private readonly _panel: vscode.WebviewPanel;
    private readonly _extensionUri: vscode.Uri;
    private _disposables: vscode.Disposable[] = [];

    private static getWebviewOptions(extensionUri: vscode.Uri): vscode.WebviewOptions {
        return {
            // Enable javascript in the webview
            enableScripts: true,

            // And restrict the webview to only loading content from our
            // extension's `webview` directory.
            localResourceRoots: [vscode.Uri.joinPath(extensionUri, 'webview')]
        };
    }

    public static createOrShow(extensionUri: vscode.Uri): SingletonWebViewPanel {
        let column = vscode.window.activeTextEditor?.viewColumn;
        if (column != undefined) {
            column += 1;
        } else {
            column = vscode.ViewColumn.One;
        }
        //const column = vscode.ViewColumn.Beside;

        // If we already have a panel, show it.
        if (SingletonWebViewPanel.currentPanel) {
            SingletonWebViewPanel.currentPanel._panel.reveal(column);
            return SingletonWebViewPanel.currentPanel;
        }

        // Otherwise, create a new panel.
        const panel = vscode.window.createWebviewPanel(
            SingletonWebViewPanel.viewType,
            'Coq Synthesis',
            column || vscode.ViewColumn.One,
            SingletonWebViewPanel.getWebviewOptions(extensionUri),
        );

        SingletonWebViewPanel.currentPanel = new SingletonWebViewPanel(panel, extensionUri);

        return SingletonWebViewPanel.currentPanel;
    }

    private constructor(panel: vscode.WebviewPanel, extensionUri: vscode.Uri) {
        this._panel = panel;
        this._extensionUri = extensionUri;

        // Listen for when the panel is disposed
        // This happens when the user closes the panel or when the panel is closed programmatically
        this._panel.onDidDispose(() => this.dispose(), null, this._disposables);
    }

    public postMessage(msg: any) {
        this._panel.webview.postMessage(msg);
    }

    public dispose() {
        SingletonWebViewPanel.currentPanel = undefined;

        // Clean up our resources
        this._panel.dispose();

        while (this._disposables.length) {
            const x = this._disposables.pop();
            if (x) {
                x.dispose();
            }
        }
    }

    public setHtml(html: string) {
        this._panel.title = 'Coq Synthesis';
        this._panel.webview.html = html;
    }

    public getResourceUri(fileName: string): vscode.Uri {
        const localUri = vscode.Uri.joinPath(this._extensionUri, 'webview', fileName)
        return this._panel.webview.asWebviewUri(localUri);
    }
}

// This method is called when your extension is activated
// Your extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {

    // Use the console to output diagnostic information (console.log) and errors (console.error)
    // This line of code will only be executed once when your extension is activated
    console.log('Congratulations, your extension "coq-synthesis-vscode" is now active!');

    console.log('extensionPath = ', context.extensionPath);
    const proverbot_dir = path.join(context.extensionPath, '..', 'proverbot9001-plugin');
    console.log('proverbot dir = ', proverbot_dir);

    // The command has been defined in the package.json file
    // Now provide the implementation of the command with registerCommand
    // The commandId parameter must match the command field in package.json
    const disposable = vscode.commands.registerCommand('coq-synthesis-vscode.helloWorld', async () => {
        // The code you place here will be executed every time your command is executed
        // Display a message box to the user
        vscode.window.showInformationMessage('Hello World from coq-synthesis-vscode!');

        const textEditor = vscode.window.activeTextEditor;
        if (textEditor == null) {
            return;
        }

        const document = textEditor.document;

        // Make the buffer read-only.  The proof search returns a range of
        // characters to overwrite with the new proof, and those positions will
        // be invalidated if the user modifies the file while the search is
        // running.
        console.log('make readonly');
        vscode.commands.executeCommand('workbench.action.files.setActiveEditorReadonlyInSession');

        const file_path = document.uri.fsPath;
        const parent_dir = path.dirname(file_path);
        const proof_line = textEditor.selection.active.line;


        // Write buffer content to a temp file.  This lets proverbot see the
        // current content even if the file hasn't been saved recently.
        const filenameBase = path.basename(file_path, '.v')
        const tempFileRandomness = crypto.randomBytes(16).toString('base64')
            .replaceAll('/', '_').replaceAll('+', '\'').replaceAll('=', '');
        const tempModuleName = `${filenameBase}__vscode_${tempFileRandomness}`;
        const tempFileName = tempModuleName + '.v';
        const tempFilePath = path.join(parent_dir, tempFileName);
        await fsPromises.writeFile(tempFilePath, document.getText(), {
            'mode': 0o600,
            'flag': 'wx',
        });
        // TODO: clean up temp file on error
        console.log('temp file = ', tempFilePath);

        console.log('starting..');
        const exitStatus = await runTerminalAsync({
            'name': 'Proofster',
            'message': 'Running proof search...\r\n',
            /*'location': {
                'viewColumn': vscode.ViewColumn.Beside,
                'preserveFocus': true,
            },*/
            'shellPath': proverbot_dir + '/venv/bin/python3',
            'shellArgs': [
                proverbot_dir + '/src/search_file.py',
                '--weightsfile', proverbot_dir + '/data/polyarg-weights.dat',
                tempFilePath,
                '--proof-line', (1 + proof_line).toString(),
                '--no-generate-report',
                '--no-resume',
            ],
            'cwd': parent_dir,
        });
        // TODO: properly handle bad exitStatus
        // TODO: make buffer writable on error or cancellation
        // TODO (style): use camelCase instead of snake_case consistently
        console.log('done', exitStatus);

        await fsPromises.unlink(tempFilePath);

        const result_path = path.join(parent_dir, 'search-report', tempModuleName + '-proofs.txt');
        const result_text = await fsPromises.readFile(result_path, {'encoding': 'utf8'});
        const result = JSON.parse(result_text);
        console.log('results', result);
        // TODO: check for success vs failure
        // TODO: only paste in the proof if the search succeeds
        console.log(' === proof ===');
        for (let cmd of result[1]['commands']) {
            console.log(cmd['tactic']);
        }
        const result_info = result[2];
        const span = result_info['span'];
        const start = document.positionAt(span[1]);
        const end = document.positionAt(span[2]);
        const span_range = new vscode.Range(start, end);
        // TODO: remove search-report files when finished

        console.log('make read-write');
        vscode.commands.executeCommand('workbench.action.files.setActiveEditorWriteableInSession');

        console.log('applying edit');
        textEditor.edit((editBuilder) => {
            let s = '';
            for (let cmd of result[1]['commands']) {
                if (s != '') {
                    s += '\n';
                }
                s += cmd['tactic'];
            }
            console.log('new text = ', s);
            editBuilder.replace(span_range, s);
        });

        const treeResultFileName =
            result_info['module_prefix'] + result_info['lemma_name'] + '.graph.json';
        const treeResultPath = path.join(parent_dir, 'search-report', treeResultFileName);
        const treeResultText = await fsPromises.readFile(treeResultPath, {'encoding': 'utf8'});
        console.log(treeResultText);
        const treeResult = JSON.parse(treeResultText);

        const panel = SingletonWebViewPanel.createOrShow(context.extensionUri);
        const treeJs = panel.getResourceUri('tree.js');
        const treeCss = panel.getResourceUri('tree.css');
        // TODO: vendor jquery and d3 instead of relying on third-party cdns
        panel.setHtml(`<!DOCTYPE html>
            <html>
            <head>
            <script src="http://code.jquery.com/jquery-1.10.2.min.js"></script>
            <script src="http://d3js.org/d3.v3.min.js"></script>
            <script src="${treeJs}"></script>
            <link href="${treeCss}" rel="stylesheet" />
            <style>
            body {
                margin: 0;
                padding: 0;
                overflow: hidden;
            }
            </style>
            <script>
            window.addEventListener('message', (event) => {
                renderTree(event.data);
            }, false);
            </script>
            </head>
            <body>
            <div id="tree-container"></div>
            </body>
            </html>
        `);
        panel.postMessage(treeResult);
    });

    context.subscriptions.push(disposable);
}

// This method is called when your extension is deactivated
export function deactivate() {}
