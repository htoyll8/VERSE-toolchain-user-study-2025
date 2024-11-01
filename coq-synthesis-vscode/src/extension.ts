// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import path from 'path';
import fs from 'fs';
import fsPromises from 'fs/promises';
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

        // TODO:
        // - Write buffer to a temp dir
        // - Read results back from temp dir

        // Make the buffer read-only.  The proof search returns a range of
        // characters to overwrite with the new proof, and those positions will
        // be invalidated if the user modifies the file while the search is
        // running.
        console.log('make readonly');
        vscode.commands.executeCommand('workbench.action.files.setActiveEditorReadonlyInSession');

        const file_path = document.uri.fsPath;
        const parent_dir = path.dirname(file_path);
        const proof_name = 'app_nil_r';

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
                file_path,
                '--proof', proof_name,
                '--no-generate-report',
                '--no-resume',
            ],
            'cwd': parent_dir,
        });
        console.log('done', exitStatus);
        const result_path = path.join(parent_dir, 'search-report', path.basename(file_path, '.v') + '-proofs.txt');
        const result_text = await fsPromises.readFile(result_path, {'encoding': 'utf8'});
        const result = JSON.parse(result_text);
        console.log('results', result);
        console.log(' === proof ===');
        for (let cmd of result[1]['commands']) {
            console.log(cmd['tactic']);
        }
        const span = result[0][4];
        const start = document.positionAt(span[1]);
        const end = document.positionAt(span[2]);
        const span_range = new vscode.Range(start, end);

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
	});

    context.subscriptions.push(disposable);
}

// This method is called when your extension is deactivated
export function deactivate() {}
