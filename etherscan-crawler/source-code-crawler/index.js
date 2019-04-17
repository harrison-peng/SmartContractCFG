

// create an Etherscan accout to get the Api-Key Token
// https://etherscan.io/myapikey
const apiKeyToken = '73DDW1BIE63UZ77S7ITNUBNYSCQMJ8HW1B';

const getJSON = require('get-json');
const fs = require('fs');

const input = JSON.parse(fs.readFileSync('result.json', 'utf8'));
const output = [];

for (let j = 0; j < 1000; j++)
	output[j] = {};

// call fff
fff(input, output);


// fff function
async function fff(input, output) {


	for (let i = 1; i < 1000; i++) {

		try {
			console.log("----");
			console.log(i);

			const address = input[i].address;

			output[i].address = address;
			output[i].result = null;

			const data = await getJSON(`https://api.etherscan.io/api?module=contract&action=getsourcecode&address=${address}&apikey=${apiKeyToken}`);
			const result = data.result;

			output[i].result = result;


		} catch (error) {

			console.log(error);
			console.log("eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee");

		}

	}

	var json = JSON.stringify(output, null, 2);
	fs.writeFileSync("source_code_output.json", json, 'utf8');
	console.log("DONE")


};





