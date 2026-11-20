import { createRequire } from 'node:module';

// The pinned Quint downloader only downloads/unpacks here; it does not launch Java.
const require = createRequire(import.meta.url);
const { fetchApalache } = require('@informalsystems/quint/dist/src/apalache.js');
const result = await fetchApalache('0.62.4', 0);
if (result.isLeft()) {
  process.stderr.write('Could not prepare the pinned Apalache distribution.\n');
  process.exitCode = 1;
}
